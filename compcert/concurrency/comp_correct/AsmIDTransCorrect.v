Require Import Coqlib Maps Errors Globalenvs AST.
Require Import Values Memory Globalenvs Events Smallstep Blockset  InjRels Footprint.

Require Import Op Registers val_casted CUAST GMemory FMemory InteractionSemantics Blockset SeqCorrect IS_local LDSim_local Localize AsmLang ASM_local Op_fp.
Require Import LDSimDefs_local.
Require Import Lia. 

Local Ltac Hsimpl:=
  repeat match goal with
         | H1:?a,H2:?a->?b|-_=>specialize (H2 H1)
         | H:_/\_|-_=> destruct H
         | H:exists _,_|-_=>destruct H
         end.
Local Ltac Esimpl:=
  repeat match goal with
         | H:_|-_/\_=>split
         | H:_|-exists _,_=>eexists
         end.
Local Ltac ex_match:=
  repeat match goal with
         | H: match ?x with _ => _ end = _ |- _ => destruct x eqn:?Hx; try discriminate
         | H:_ |- context[match ?x with _ => _ end] => destruct x eqn:?Hx;try discriminate
         end;try congruence.
Definition id_trans_asm: @seq_comp AsmLang AsmLang :=
  fun cu => assertion (nodup_gd_ident (cu_defs cu));
           assertion (nodup_ef (cu_defs cu));
           OK cu.

Import Maps Integers Values Asm ASM_local Injections Footprint LDSimDefs LDSimDefs_local 
       AST Memory MemClosures_local InjRels val_casted.

Definition match_regset (rs rs': Asm.regset) : Prop :=
  forall r, Val.lessdef (rs # r) (rs' # r).

Lemma set_match_regset:
  forall rs rs' r v v',
    match_regset rs rs' ->
    Val.lessdef v v' ->
    match_regset (rs # r <- v) (rs' # r <- v').
Proof.
  intros. intro r'.
  destruct (Pregmap.elt_eq r r');
    [subst; repeat rewrite Pregmap.gss| repeat rewrite Pregmap.gso]; auto.
Qed.

Lemma set_res_match_regset:
  forall br rs rs' v v',
    match_regset rs rs' ->
    Val.lessdef v v' ->
    match_regset (set_res br v rs) (set_res br v' rs').
Proof.
  induction br; intros; simpl; auto using set_match_regset.
  apply IHbr2. apply IHbr1. auto. inv H0; simpl; auto. inv H0; simpl; auto.
Qed.

Lemma undef_match_regset:
  forall rl rs rs',
    match_regset rs rs' ->
    match_regset (undef_regs rl rs) (undef_regs rl rs').
Proof. induction rl; intros; auto. simpl. apply IHrl; auto using set_match_regset. Qed.

Lemma offset_ptr_lessdef:
  forall v v' i, Val.lessdef v v' -> Val.lessdef (Val.offset_ptr v i) (Val.offset_ptr v' i).
Proof. inversion 1; auto. Qed.

Lemma match_regset_lessdef:
  forall rs rs' r, match_regset rs rs' -> Val.lessdef (rs # r) (rs' # r).
Proof. auto. Qed.

Lemma eval_addrmode_lessdef:
  forall ge a rs rs',
    match_regset rs rs' ->
    Val.lessdef (eval_addrmode ge a rs) (eval_addrmode ge a rs').
Proof.
  unfold eval_addrmode, eval_addrmode64, eval_addrmode32.
  destruct Archi.ptr64; intros;
    destruct a as [[r1|] [[r2 z1]|] [z2 | [id ofs]]];
    repeat apply Val.addl_lessdef; repeat apply Val.add_lessdef; auto;
      destruct zeq; auto; destruct (H r2); simpl; auto.
Qed.
Lemma eval_addrmode32_lessdef:
  forall ge a rs rs',
    match_regset rs rs' ->
    Val.lessdef (eval_addrmode32 ge a rs) (eval_addrmode32 ge a rs').
Proof.
  unfold eval_addrmode, eval_addrmode64, eval_addrmode32.
  destruct Archi.ptr64; intros;
    destruct a as [[r1|] [[r2 z1]|] [z2 | [id ofs]]];
    repeat apply Val.addl_lessdef; repeat apply Val.add_lessdef; auto;
      destruct zeq; auto; destruct (H r2); simpl; auto.
Qed.
Lemma eval_addrmode64_lessdef:
  forall ge a rs rs',
    match_regset rs rs' ->
    Val.lessdef (eval_addrmode64 ge a rs) (eval_addrmode64 ge a rs').
Proof.
  unfold eval_addrmode, eval_addrmode64, eval_addrmode32.
  destruct Archi.ptr64; intros;
    destruct a as [[r1|] [[r2 z1]|] [z2 | [id ofs]]];
    repeat apply Val.addl_lessdef; repeat apply Val.add_lessdef; auto;
      destruct zeq; auto; destruct (H r2); simpl; auto.
Qed.
Definition local_content_eq (ge:genv) m m' :=
  forall b ofs, Ple (Genv.genv_next ge) b ->
           Mem.perm m b ofs Cur Readable ->
           ZMap.get ofs ((Mem.mem_contents m) !! b) = ZMap.get ofs ((Mem.mem_contents m') !! b).

Definition local_perm_eq (ge:genv) m m' :=
  forall b, Ple (Genv.genv_next ge) b ->
       (Mem.mem_access m) !! b = (Mem.mem_access m') !! b.
Lemma exec_load_fp_match:
  forall ge chunk a rs rs' m rs2 m2 rd,
    exec_load ge chunk m a rs rd = Next rs2 m2 ->
    match_regset rs rs'->
    FP.subset (exec_load_fp ge chunk a rs')(exec_load_fp ge chunk a rs).
Proof.
  unfold exec_load_fp,exec_load, FMemOpFP.loadv_fp.
  intros.
  ex_match;try apply FP.subset_emp.
  eapply eval_addrmode_lessdef in H0.
  inv H0. erewrite H3,Hx0 in Hx1. inv Hx1. apply FP.subset_refl.
  rewrite <- H2 in Hx1. inv Hx1.
Qed.  

  
Lemma exec_load_match:
  forall ge chunk a rd m1 rs1 m2 rs2 m1' rs1',
    exec_load ge chunk m1 a rs1 rd = Next rs2 m2 ->
    Mem.extends m1 m1' ->
    match_regset rs1 rs1' ->
    exists rs2' m2', exec_load ge chunk m1' a rs1' rd = Next rs2' m2' /\
                Mem.extends m2 m2' /\
                match_regset rs2 rs2'.
Proof.
  unfold exec_load. intros until 1.
  destruct Mem.loadv eqn:LOAD; inv H. intros.
  exploit (eval_addrmode_lessdef ge a rs1 rs1'); eauto. 
  destruct (eval_addrmode ge a rs1); try discriminate. intro A. inv A.
  eapply Mem.loadv_extends in LOAD; eauto. destruct LOAD as [v' [LOAD VALLESSDEF]].
  rewrite LOAD.
  Esimpl;eauto.
  unfold nextinstr_nf, nextinstr.
  eapply set_match_regset; auto using undef_match_regset, offset_ptr_lessdef, set_match_regset, match_regset_lessdef.
Qed.
      
Local Ltac solv_eq:=
  match goal with
  | [H1: ?P , H2 : ?P |- _] => clear H1
  | [H1: ?P = _, H2: ?P = _ |- _] =>
    rewrite H1 in H2; inv H2
  | [H1: ?P = _ , H2: _ = ?P |- _] =>
    rewrite H1 in H2; inv H2
  | H: Vptr _ _ = Vptr _ _ |- _=> inv H
  | H: Vint _ = Vint _|- _ => inv H
  | H: Vlong _ = Vlong _|- _ => inv H
  | H: Vfloat _ = Vfloat _|- _ => inv H
  | H: Vsingle _ = Vsingle _|- _ => inv H
  | H: Next _ _ = Next _ _|- _=> inv H
  | H: ?p = _ |- context[match ?p with _ => _ end] => rewrite H
  end;try discriminate.
Lemma match_regset_rs_val:
  forall rs rs' r,
    match_regset rs rs'->
    rs' r = Vundef->
    rs r = Vundef.
Proof.
  intros. eapply match_regset_lessdef with(r:=r) in H.
  inv H; congruence.
Qed.
Lemma match_regset_rs_val2:
  forall rs rs' r i,
    match_regset rs rs'->
    rs r = i->
    i <> Vundef ->
    rs' r = i.
Proof.
  intros. eapply match_regset_lessdef with(r:=r) in H.
  inv H; congruence.
Qed.
Lemma weak_valid_pointer_fp_univ_subset:
  forall m b i,
    FP.subset (MemOpFP.weak_valid_pointer_fp m b i) {|FP.cmps := Locs.univ;FP.reads := Locs.emp;FP.writes := Locs.emp;FP.frees := Locs.emp |}.
Proof.
  unfold MemOpFP.weak_valid_pointer_fp,FMemOpFP.valid_pointer_fp,FMemOpFP.range_locset;intros.
  ex_match;simpl;econstructor;simpl;try apply Locs.subset_refl;Locs.unfolds;auto.
Qed.
Lemma union_subset_split:
  forall fp1 fp2 fp,
    FP.subset fp1 fp ->
    FP.subset fp2 fp ->
    FP.subset (FP.union fp1 fp2) fp.
Proof.
  destruct fp1,fp2;intros;inv H;inv H0;simpl in *.
  unfold FP.union. simpl.
  constructor;simpl;Locs.unfolds; intros.
  destruct cmps eqn:?. eapply subset_cmps;eauto.
  destruct cmps0 eqn:?;simpl in H;inv H. eapply subset_cmps0;eauto.
  destruct reads eqn:?. eapply subset_reads;eauto.
  destruct reads0 eqn:?;simpl in H;inv H. eapply subset_reads0;eauto.
  destruct writes eqn:?. eapply subset_writes;eauto.
  destruct writes0 eqn:?;simpl in H;inv H. eapply subset_writes0;eauto.
  destruct frees eqn:?. eapply subset_frees;eauto.
  destruct frees0 eqn:?;simpl in H;inv H. eapply subset_frees0;eauto.
Qed.
Lemma valid_pointer_fp_univ_subset:
  forall b i,
    FP.subset (MemOpFP.valid_pointer_fp b i) {|FP.cmps := Locs.univ;FP.reads := Locs.emp;FP.writes := Locs.emp;FP.frees := Locs.emp |}.
Proof.
  unfold FMemOpFP.valid_pointer_fp,FMemOpFP.range_locset;intros.
  ex_match;simpl;econstructor;simpl;try apply Locs.subset_refl;Locs.unfolds;auto.
Qed.

Lemma exec_store_fp_match:
  forall ge chunk a rs rs' m rs2 m2 rd dd,
    exec_store ge chunk m a rs rd  dd= Next rs2 m2 ->
    match_regset rs rs'->
    FP.subset (exec_store_fp ge chunk a rs')(exec_store_fp ge chunk a rs).
Proof.
  unfold exec_store_fp,exec_store, FMemOpFP.storev_fp.
  intros.
  ex_match;try apply FP.subset_emp.
  eapply eval_addrmode_lessdef in H0.
  inv H0. erewrite H3,Hx0 in Hx1. inv Hx1. apply FP.subset_refl.
  rewrite <- H2 in Hx1. inv Hx1.
Qed.  

Lemma exec_store_match:
  forall ge chunk a r1 destroyed m1 rs1 m2 rs2 m1' rs1',
    exec_store ge chunk m1 a rs1 r1 destroyed = Next rs2 m2 ->
    Mem.extends m1 m1' ->
    match_regset rs1 rs1' ->
    exists rs2' m2', exec_store ge chunk m1' a rs1' r1 destroyed = Next rs2' m2' /\
                Mem.extends m2 m2' /\
                match_regset rs2 rs2'.
Proof.
  unfold exec_store. intros until 1.
  destruct Mem.storev eqn:STORE; inv H. intros.
  exploit (eval_addrmode_lessdef ge a rs1 rs1'); eauto.
  destruct (eval_addrmode ge a rs1); try discriminate. intro A. inv A.
  eapply Mem.storev_extends in STORE; eauto. destruct STORE as [m2' [STORE EXT]].
  rewrite STORE. do 2 eexists. split. eauto. split. eauto.
  unfold nextinstr_nf, nextinstr.
  eapply set_match_regset; auto using undef_match_regset, offset_ptr_lessdef, set_match_regset, match_regset_lessdef.
Qed.

Lemma cons_lessdef:
  forall v v' f,
    f Vundef = Vundef ->
    Val.lessdef v v'->
    Val.lessdef (f v)(f v').
Proof.
  inversion 2;subst;auto.
  intros. rewrite H. auto.
Qed.
Lemma lessdef_maketotal_f:
  forall r r' f,
    f Vundef = Some Vundef \/ f Vundef = None ->
    Val.lessdef r r'->
    Val.lessdef (Val.maketotal (f r))(Val.maketotal (f r')).
Proof.
  intros.
  inv H0; auto.
  destruct H;rewrite H;auto.
Qed.
Lemma lessdef_binop:
  forall a a' b b' f,
    (forall a b, a = Vundef \/ b = Vundef ->f a b = Vundef) ->
    Val.lessdef a a'->
    Val.lessdef b b'->
    Val.lessdef (f a b)(f a' b').
Proof.
  intros.
  inv H1;inv H0;auto;erewrite H;eauto.
Qed.
Lemma onceset_match_regset:
  forall rs rs' rd,
    match_regset rs rs'->
    match_regset rs # rd <- Vundef rs'.
Proof.
  unfold match_regset.
  intros.
  destruct (Pregmap.elt_eq r rd). subst.
  rewrite Pregmap.gss. constructor.
  rewrite Pregmap.gso;auto.
Qed.
Ltac solv_rs:=
  match goal with
  | H0:match_regset ?rs ?rs',H1:?rs' ?a = Vundef |- _ =>
    eapply match_regset_rs_val in H1;eauto;try discriminate;solv_eq
  | H0:match_regset ?rs ?rs',H1:?rs ?a = _ _  |- _ =>
    eapply match_regset_rs_val2 in H1;try apply H0;eauto;try discriminate;solv_eq
  | H0:match_regset ?rs ?rs',H1:?rs ?a = _ _ _ |- _ =>
    eapply match_regset_rs_val2 in H1;try apply H0;eauto;try discriminate;solv_eq
  end.
Lemma eval_testcond_true_regset:
  forall rs rs' c res,
    match_regset rs rs'->
    res <> None ->
    eval_testcond c rs = res->
    eval_testcond c rs' = res.
Proof.
  intros.
  unfold eval_testcond in *.
  repeat match goal with
         | H: match ?a with _ => _ end = _ |- _ =>
           destruct a eqn:?; try congruence; repeat solv_rs; auto
         end.
Qed.
Lemma eval_testcond_false_regset:
  forall rs rs' c ,
    match_regset rs rs'->
    eval_testcond c rs' = None ->
    eval_testcond c rs = None.
Proof.
  intros.
  destruct (eval_testcond c rs)eqn:?.
  eapply eval_testcond_true_regset in Heqo;eauto.
  rewrite H0 in Heqo. discriminate.
  discriminate.
  auto.
Qed.
Lemma eval_testcond_lessdef:
  forall c rs rs',
    match_regset rs rs' ->
    Val.lessdef (Val.of_optbool (eval_testcond c rs))(Val.of_optbool(eval_testcond c rs')).
Proof.
  intros.
  destruct (eval_testcond c rs) eqn:?;auto.
  eapply eval_testcond_true_regset in Heqo;eauto;try congruence.
  rewrite Heqo. constructor.
Qed.  
Ltac solv_regset:=try
  match goal with
  | |- match_regset (_ # _ <- _) (_ # _ <- _) => apply set_match_regset; auto; solv_regset
  | |- match_regset (?a _ # _ <- _) (?a _ # _ <- _) => apply set_match_regset; auto; solv_regset
  | |- match_regset ( _ # _ <- _) ?a' => apply onceset_match_regset;auto;solv_regset
  | |- match_regset (set_res _ _ _) (set_res _ _ _) => apply set_res_match_regset; auto; solv_regset
  | |- match_regset (undef_regs _ _) (undef_regs _ _) => apply undef_match_regset; auto; solv_regset
  | |- match_regset (nextinstr _)(nextinstr _) => apply set_match_regset;auto;solv_regset
  | |- Val.lessdef (Val.offset_ptr _ _) (Val.offset_ptr _ _) => apply offset_ptr_lessdef; auto; solv_regset
  | |- Val.lessdef (Val.zero_ext ?a _)(Val.zero_ext ?a _) => apply Val.zero_ext_lessdef; auto; solv_regset
  | |- Val.lessdef (Val.sign_ext ?a _)(Val.sign_ext ?a _) => apply Val.sign_ext_lessdef; auto; solv_regset
  | |- Val.lessdef (Val.of_optbool (eval_testcond ?c ?rs))(Val.of_optbool(eval_testcond ?c ?rs')) => apply eval_testcond_lessdef;solv_regset
  | |- Val.lessdef (Val.maketotal (?a (?rs ?b)))(Val.maketotal (?a (?rs' ?b))) =>
    eapply lessdef_maketotal_f;eauto;solv_regset
  | |- Val.lessdef (eval_addrmode32 ?ge ?a ?rs1) (eval_addrmode32 ?ge ?a ?rs1')=>
    eapply eval_addrmode32_lessdef;eauto;solv_regset
  | |- Val.lessdef (eval_addrmode64 ?ge ?a ?rs1) (eval_addrmode64 ?ge ?a ?rs1')=>
    eapply eval_addrmode64_lessdef;eauto;solv_regset
  | |- Val.lessdef (eval_addrmode ?ge ?a ?rs1) (eval_addrmode ?ge ?a ?rs1')=>
    eapply eval_addrmode_lessdef;eauto;solv_regset
  | |- Val.lessdef (?f _ _) (?f _ _)=>
    eapply lessdef_binop;eauto;solv_regset
  | |- Val.lessdef (?f _)(?f _) => apply cons_lessdef;auto;solv_regset
  | |- Val.lessdef (_ # _) (_ # _) => eapply match_regset_lessdef; solv_regset
  end.


Ltac inv_next:=
  match goal with
  | H: Next _ _ = Next _ _ |- _ => inv H
  | H: Stuck = Next _ _ |- _ => inv H
  | H: Next _ _ = Stuck |- _ => inv H
  end.

 


Lemma regset_jmptbl:
  forall rs rs' b i,
    match_regset rs rs'->
    (rs # RAX <- Vundef) # RDX <- Vundef PC = Vptr b i ->
    (rs' # RAX <- Vundef) # RDX <- Vundef PC = Vptr b i.
Proof.
  intros.
  rewrite Pregmap.gso in *;try congruence.
  rewrite Pregmap.gso in *;try congruence.
  solv_rs.
Qed.
Lemma valid_pointer_extends:
  forall m m' b i,
    Mem.extends m m'->
    Mem.valid_pointer m b i = true ->
    Mem.valid_pointer m' b i = true.
Proof.
  intros.
  eapply Mem.valid_pointer_extends in H;eauto.
Qed.

Lemma weak_valid_pointer_extends:
  forall m m' b i,
    Mem.extends m m' ->
    Mem.valid_pointer m b i || Mem.valid_pointer m b (i-1) = true->
    Mem.valid_pointer m' b i || Mem.valid_pointer m' b (i-1) = true.
Proof.
  intros.
  destruct Mem.valid_pointer eqn:?.
  eapply valid_pointer_extends in Heqb0 as ?;eauto.
  rewrite H1;auto.
  
  destruct (Mem.valid_pointer m b (i-1)) eqn:?.
  eapply valid_pointer_extends in Heqb1 as ?;eauto.
  rewrite H1;auto with bool.
  auto.
Qed.
Lemma union_refl_eq:  forall l, Locs.union l l = l.  intros;eapply Locs.locs_eq. eapply Locs.union_refl. Defined.
Lemma fp_union_refl_eq:
  forall fp,
    FP.union fp fp = fp.
Proof.
  destruct fp. unfold FP.union.
  simpl.
  f_equal;apply union_refl_eq.
Qed.

Lemma compare_floats_regset_match:
  forall i j rs rs' i' j',
    match_regset rs rs'->
    Val.lessdef i i'->
    Val.lessdef j j'->
    match_regset (compare_floats i j rs)(compare_floats i' j' rs').
Proof.
  intros;unfold compare_floats.
  inv H0; inv H1; auto;
    destruct i',j'; simpl; try solv_regset.
Qed.
Lemma compare_floats32_regset_match:
  forall i j rs rs' i' j',
    match_regset rs rs'->
    Val.lessdef i i'->
    Val.lessdef j j'->
    match_regset (compare_floats32 i j rs)(compare_floats32 i' j' rs').
Proof.
  intros;unfold compare_floats.
  inv H0;inv H1;simpl; auto;
    destruct i',j';simpl;try solv_regset.
Qed.
Ltac check:=try(Esimpl;eauto;try apply FP.subset_refl;try solv_regset;auto;fail).
Ltac eval_check:=
  repeat match goal with
         | H1: match_regset ?rs ?rs', H2: eval_testcond _ ?rs = Some _ |- _ =>
           eapply eval_testcond_true_regset in H2;try apply H1;eauto;try congruence
         end;try solv_eq;check.
Lemma lessdef_inversion:
  forall i j,
    Val.lessdef i j ->
    i = j \/ i = Vundef.
Proof.
  intros.
  inv H;auto.
Qed. 
Lemma check_vundef_lessdef:
  forall i j i' j',
    Val.lessdef i j ->
    Val.lessdef i' j'->
    check_vundef i i' = true ->
    check_vundef j j' = true.
Proof.
  intros.
  apply lessdef_inversion in H as [];apply lessdef_inversion in H0 as [];subst;simpl in *;try discriminate;auto.
  destruct j;try discriminate.
Qed.
Lemma extends_compare_ints_fp_match:
  forall i j i' j' m m',
    check_vundef i j = true->
    Mem.extends m m'->
    Val.lessdef i i'->
    Val.lessdef j j'->
    FP.subset(compare_ints_fp i' j' m')(compare_ints_fp i j m).
Proof.
  intros.
  unfold compare_ints_fp,ValFP.cmpu_bool_fp_total.
  ex_match;try apply FP.subset_refl;subst.
  all : subst;repeat match goal with
            | H: Val.lessdef _ _ |- _ => inv H
                  end.
  all :repeat rewrite FP.emp_union_fp;try apply FP.subset_emp.
  all :repeat rewrite FP.fp_union_emp;try apply FP.subset_refl;try solv_eq;try apply FP.subset_refl.
  all :try apply FP.subset_parallel_union;try apply union_subset_split.
  all :try rewrite fp_union_refl_eq;try apply weak_valid_pointer_fp_univ_subset;try apply valid_pointer_fp_univ_subset.

  all : try eapply MemOpFP.weak_valid_pointer_extend_subset;eauto.
  all : try (eapply FP.subset_union_subset;eapply MemOpFP.weak_valid_pointer_extend_subset;eauto).
  all : try (rewrite FP.union_comm_eq;eapply FP.subset_union_subset;eapply MemOpFP.weak_valid_pointer_extend_subset;eauto).
Qed.


Lemma extends_compare_longs_fp_match:
  forall i j i' j' m m',
    check_vundef i j = true->
    Mem.extends m m'->
    Val.lessdef i i'->
    Val.lessdef j j'->
    FP.subset(compare_longs_fp i' j' m')(compare_longs_fp i j m).
Proof.
  intros.
  unfold compare_longs_fp,ValFP.cmplu_bool_fp_total.
  ex_match;try apply FP.subset_refl;subst.
  all : repeat match goal with
               | H: Val.lessdef _ _ |- _ => inv H
               end.
  all : repeat rewrite FP.emp_union_fp;try apply FP.subset_emp.
Qed.

Lemma extends_check_compare_ints_match:
  forall i j i' j' m m',
    Mem.extends m m' ->
    Val.lessdef i i' ->
    Val.lessdef j j' ->
    check_vundef i j = true ->
    check_compare_ints i j m = true ->
    check_compare_ints i' j' m' = true.
Proof.
  unfold check_compare_ints. intros.
  destruct (Val.cmpu_bool (Mem.valid_pointer m) Ceq i j) eqn:A; [|inv H3].
  assert (forall b ofs, Mem.valid_pointer m b ofs = true -> Mem.valid_pointer m' b ofs = true).
  { intros. destruct H. destruct mext_inj. unfold Mem.valid_pointer in *.
    destruct Mem.perm_dec in H4; [clear H4|inv H4]. 
    eapply mi_perm in p; unfold inject_id; eauto.
    rewrite <- Zplus_0_r_reverse in p. destruct Mem.perm_dec; auto. }
  exploit Val.cmpu_bool_lessdef. eauto. exact H0. exact H1. exact A.
  intro C. rewrite C. clear C. auto.
Qed.
    
Lemma extends_compare_ints_regset_match:
  forall i j rs rs' m m' i' j' (CK:check_vundef i j = true),
    match_regset rs rs'->
    Mem.extends m m'->
    Val.lessdef i i'->
    Val.lessdef j j'->
    match_regset (compare_ints i j rs m)(compare_ints i' j' rs' m'). 
Proof.
  unfold compare_ints;intros;solv_regset.
  3,4:intros [] [] [] ;auto;congruence.
  unfold Val.cmpu,Val.cmpu_bool.
  inv H1;inv H2;auto; destruct i',j'; auto.
  all : ex_match;try constructor.

  all : try (destruct Int.eq;simpl in *;try congruence;eapply weak_valid_pointer_extends in Hx0;eauto;congruence);try solv_eq.
  
  destruct ( (Mem.valid_pointer m b (Ptrofs.unsigned i) || Mem.valid_pointer m b (Ptrofs.unsigned i - 1)) ) eqn:?;try congruence.
  eapply weak_valid_pointer_extends in Heqb1 as ?;eauto;try congruence.
  rewrite H1 in *;simpl in *;try congruence.
  eapply weak_valid_pointer_extends in Hx1;eauto. congruence.
  
  simpl in *. congruence.
  destruct ( Mem.valid_pointer m b (Ptrofs.unsigned i)) eqn:?;simpl in *;try congruence;destruct ( Mem.valid_pointer m b0 (Ptrofs.unsigned i0)) eqn:?;simpl in *;try congruence.
  eapply valid_pointer_extends in Heqb1;eauto.
  eapply valid_pointer_extends in Heqb0;eauto.
  rewrite Heqb0,Heqb1 in Hx2. simpl in Hx2. congruence.

  unfold Val.cmpu,Val.cmpu_bool.
  inv H1;inv H2;auto;destruct i',j';auto.
  all : ex_match;try constructor;subst.
  destruct ( (Mem.valid_pointer m b0 (Ptrofs.unsigned i) || Mem.valid_pointer m b0 (Ptrofs.unsigned i - 1)) ) eqn:?;simpl in * ;try congruence;destruct ( (Mem.valid_pointer m b0 (Ptrofs.unsigned i0) || Mem.valid_pointer m b0 (Ptrofs.unsigned i0 - 1)) ) eqn:?;simpl in * ;try congruence.
  eapply weak_valid_pointer_extends in Heqb as ?;eauto;try congruence.
  eapply weak_valid_pointer_extends in Heqb0 as ?;eauto;try congruence.
  rewrite H1 in *;simpl in *;try congruence.
Qed.  
  
  
Lemma extends_compare_longs_regset_match:
  forall i j rs rs' m m' i' j' (CK:check_vundef i j = true),
    match_regset rs rs'->
    Mem.extends m m'->
    Val.lessdef i i'->
    Val.lessdef j j'->
    match_regset (compare_longs i j rs m)(compare_longs i' j' rs' m').
Proof.
  intros;unfold compare_longs.
  solv_regset.
  3 ,4: intros [] [] [];auto;congruence.

  1 ,2: unfold Val.cmplu, Val.cmplu_bool;
    inv H1; inv H2; destruct i', j'; try constructor.
Qed.

Lemma compare_longs_regset_match:
  forall i j rs rs' m m',
    match_regset rs rs'->
    Mem.extends m m'->
    match_regset (compare_longs (rs i)(rs j) rs m)(compare_longs (rs' i)(rs' j) rs' m').
Proof.
  intros.
  unfold compare_longs.
  solv_regset.
  3 ,4: intros [] [] [];auto;congruence.
  1, 2: pose proof (H i) as H1;  pose proof (H j) as H2; inv H1; inv H2; try constructor.
  1 ,2: destruct (rs i), (rs' j); try constructor.
Qed.

Local Notation empfp:=FP.emp.
Ltac resolvfp:=
  match goal with
  | H: ?a = ?b , H2: FP.subset _ ?a |- _ => rewrite H in H2; resolvfp
  | |- context[FP.union _ empfp] => rewrite FP.fp_union_emp; resolvfp
  | |- context[FP.union empfp _] => rewrite FP.emp_union_fp; resolvfp
  | H: Some _ = Some _ |- _ => inv H; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- Injections.FPMatch' ?mu (FP.union ?fp1 _) (FP.union ?fp1' _) => 
    eapply Injections.fp_match_union'; resolvfp
  | H: Injections.FPMatch' _ ?fp1 ?fp1' |- Injections.FPMatch' ?mu (FP.union ?fp1 _) (FP.union ?fp1' _) => 
    eapply Injections.fp_match_union'; auto; resolvfp
  | H: Injections.FPMatch' _ ?fp1 ?fp1' |- Injections.FPMatch' ?mu (FP.union ?fp1 _) ?fp1' => 
    eapply Injections.fp_match_union_S'; auto; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- FP.subset (FP.union ?fp1' _) (FP.union ?fp1 _) => 
    eapply FP.subset_parallel_union; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- FP.subset (FP.union ?fp1' _) (FP.union (FP.union ?fp1 _) _) => 
    eapply FP.subset_parallel_union; resolvfp
  | H: FP.subset ?fp1' ?fp1 |- FP.subset (FP.union (FP.union ?fp1' _) _) (FP.union (FP.union ?fp1 _) _)=> 
    eapply FP.subset_parallel_union; resolvfp
  | H: FP.subset ?fp ?fp' |- FP.subset ?fp (FP.union ?fp1 ?fp') =>
    rewrite FP.union_comm_eq; resolvfp
  | H: FP.subset ?fp ?fp' |- FP.subset ?fp (FP.union ?fp' _) =>
    apply FP.subset_union_subset; auto
  | |- Injections.FPMatch' _ _ empfp => apply Injections.fp_match_emp'
  | H: FP.subset ?fp1 ?fp2 |- Injections.FPMatch' _ ?fp2 ?fp1 =>
    apply Injections.fp_match_subset_T' with fp2; try exact H; resolvfp
  | H: FP.subset ?fp2 ?fp1 |- Injections.FPMatch' _ (FP.union ?fp1 _) ?fp2 =>
    apply Injections.fp_match_union_S'; resolvfp
  | H: FP.subset ?fp2 ?fp1 |- Injections.FPMatch' _ ?fp1 (FP.union ?fp2 _) =>
    apply Injections.fp_match_union_T'; resolvfp
  | H: FP.subset ?fp2 ?fp1 |- Injections.FPMatch' _ ?fp1 (FP.union (FP.union ?fp2 _) _) =>
    apply Injections.fp_match_union_T'; resolvfp
  | H: FP.subset ?fp2 ?fp1 |- Injections.FPMatch' _ (FP.union ?fp1 _) (FP.union (FP.union ?fp2 _) _) =>
    apply Injections.fp_match_union'; resolvfp                                          
  | H: (forall b, Bset.belongsto (FP.blocks ?fp2) _ -> ~ Injections.SharedTgt ?mu _)
    |- Injections.FPMatch' _ _ ?fp2 =>
    apply Injections.fp_match_local_block; auto                                          
  | |- FP.subset ?fp ?fp => apply FP.subset_refl
  | H: fp_inject _ ?fp ?fp', H': proper_mu _ _ _ _ |- Injections.FPMatch' _ ?fp ?fp' =>
    eapply fp_inject_fp_match; inv H'; eauto
  | H: fp_inject inject_id ?fp ?fp'|- FP.subset ?fp' ?fp =>
    apply fp_inject_id_fp_subset
  | H: proper_mu _ _ _ _ |- Injections.FPMatch' _ ?fp ?fp => inv H; eapply fp_match_id; eauto
  | _ => idtac
  end.

Ltac eresolvfp:= resolvfp; eauto.


Ltac resvalid:=
  match goal with
  (** valid blocks *)
  | H: (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m1 x), H': Mem.free ?m1 _ _ _ = Some ?m2
    |- (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m2 x)
    => let X := fresh in
      intros ? X; apply H in X; eapply Mem.valid_block_free_1; eauto
  | H: (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m1 x), H': Mem.alloc ?m1 _ _ = (?m2,_)
    |- (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m2 x)
    => let X := fresh in
      intros ? X; apply H in X; eapply Mem.valid_block_alloc; eauto
  | H: (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m1 x), H': Mem.store _ ?m1 _ _ _ = Some ?m2
    |- (forall x, Bset.belongsto ?S x -> Mem.valid_block ?m2 x)
    => let X := fresh in
      intros ? X; apply H in X; eapply Mem.store_valid_block_1; eauto
  (** Mem inv *)
  | H1: Mem.store _ ?m1 _ _ _ = Some ?m2,
        H2: Mem.store _ ?m1' _ _ _ = Some ?m2',
            H3: proper_mu _ _ _ _ 
    |- MemClosures_local.unmapped_closed _ ?m2 ?m2'
    => inv H3; eapply MemClosures_local.store_val_inject_unmapped_closed_preserved;
      try (rewrite Z.add_0_r);  try eassumption;
      try (compute; eauto; fail); try Lia.lia
  | H1: Mem.free ?m1 _ _ _ = Some ?m2,
        H2: Mem.free ?m1' _ _ _ = Some ?m2',
            H3: proper_mu _ _ _ _ 
    |- MemClosures_local.unmapped_closed _ ?m2 ?m2'
    => inv H3; eapply MemClosures_local.free_inject_unmapped_closed_preserved; eauto;
      try (rewrite Z.add_0_r);  try eassumption;
      try (compute; eauto; fail); try Lia.lia
  | H1: Mem.alloc ?m1 _ _ = (?m2, _),
        H2: Mem.alloc ?m1' _ _ = (?m2', _),
            H3: proper_mu _ _ _ _
    |- MemClosures_local.unmapped_closed _ ?m2 ?m2'
    => inv H3; eapply MemClosures_local.unchanged_on_unmapped_closed_preserved; eauto;
      try (eapply Mem.alloc_unchanged_on; eauto; fail)
  | _ => idtac
  end.
  
Lemma exec_instr_valid_block:
  forall ge f i rs m rs' m' mu,
    exec_instr ge f i rs m = Next rs' m'->
    (forall b : block, Bset.belongsto (SharedSrc mu) b -> Mem.valid_block m b)->
    forall b : block, Bset.belongsto (SharedSrc mu) b ->
                 Mem.valid_block m' b.
Proof.
  unfold exec_instr;intros until mu.
  intros ? ?.
  ex_match;simpl in *;try solv_eq;auto;try resvalid.
  all : unfold exec_load,exec_store,Mem.storev,goto_label in *;ex_match;try solv_eq;try resvalid;auto.
  intros.
  eapply Mem.store_valid_block_1; eauto.
  eapply Mem.store_valid_block_1;eauto.
  eapply Mem.valid_block_alloc;eauto.
Qed.
Lemma exec_instr_valid_block2:
  forall ge f i rs m rs' m' mu,
    exec_instr ge f i rs m = Next rs' m'->
    (forall b : block, Bset.belongsto (SharedTgt mu) b -> Mem.valid_block m b)->
    forall b : block, Bset.belongsto (SharedTgt mu) b ->
                 Mem.valid_block m' b.
Proof.
  unfold exec_instr;intros until mu.
  intros ? ?.
  ex_match;simpl in *;try solv_eq;auto;try resvalid.
  all : unfold exec_load,exec_store,Mem.storev,goto_label in *;ex_match;try solv_eq;try resvalid;auto.
  intros.
  eapply Mem.store_valid_block_1; eauto.
  eapply Mem.store_valid_block_1;eauto.
  eapply Mem.valid_block_alloc;eauto.
Qed.
Lemma exec_locked_instr_valid_block:
  forall ge i rs m rs' m' mu,
    exec_locked_instr ge i rs m = Next rs' m'->
    (forall b : block, Bset.belongsto (SharedSrc mu) b -> Mem.valid_block m b)->
    forall b : block, Bset.belongsto (SharedSrc mu) b ->
                 Mem.valid_block m' b.
Proof.
  unfold exec_locked_instr;intros until mu.
  intros ? ?.
  ex_match;simpl in *;try solv_eq;auto;try resvalid.
  all : unfold exec_load,exec_store,Mem.storev,goto_label in *;ex_match;try solv_eq;try resvalid;auto.
Qed.
Lemma exec_locked_instr_valid_block2:
  forall ge i rs m rs' m' mu,
    exec_locked_instr ge i rs m = Next rs' m'->
    (forall b : block, Bset.belongsto (SharedTgt mu) b -> Mem.valid_block m b)->
    forall b : block, Bset.belongsto (SharedTgt mu) b ->
                 Mem.valid_block m' b.
Proof.
  unfold exec_locked_instr;intros until mu.
  intros ? ?.
  ex_match;simpl in *;try solv_eq;auto;try resvalid.
  all : unfold exec_load,exec_store,Mem.storev,goto_label in *;ex_match;try solv_eq;try resvalid;auto.
Qed.

    
Section MS.
  Variable cu: Asm_comp_unit.
  Variable ge:Genv.t ASM_local.fundef unit.

  Hypothesis SGEINIT: globalenv_generic cu ge.
  Inductive match_core : core*mem -> core*mem -> Prop :=
  | match_core_state: forall rs rs' lf m m',
      match_regset rs rs' ->
      Mem.extends m m'->
      match_core (Core_State rs lf,m) (Core_State rs' lf,m')
  | match_core_callin: forall fb args tys retty m m',
      Mem.extends m m'->
      match_core (Core_CallstateIn fb args tys retty,m) (Core_CallstateIn fb args tys retty,m')
  | match_core_callout: forall ef args args' rs rs' lf m m',
      Mem.extends m m' ->
      match_regset rs rs' ->
      Val.lessdef_list args args'->
      match_core (Core_CallstateOut ef args rs lf,m) (Core_CallstateOut ef args' rs' lf,m')
  | match_core_lockstate: forall rs rs' signal lf m m',
      Mem.extends m m'->
      match_regset rs rs' ->
      match_core (Core_LockState rs signal lf,m) (Core_LockState rs' signal lf,m')
  .

  Definition MS (b:bool)(i:nat) mu fp fp' cm cm': Prop :=
    match_core cm cm' /\
    Injections.FPMatch' mu fp fp' /\
    let (c, m) := cm in
    let (c', m') := cm' in
    (forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b) /\
    (forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block m' b) /\
    (proper_mu ge ge inject_id mu) /\
    (MemClosures_local.unmapped_closed mu m m').
  
 

End MS.

Lemma exec_instr_match:
  forall i f ge m1 m2 rs1 rs2 m1' rs1',
    exec_instr ge f i rs1 m1 = Next rs2 m2 ->
    Mem.extends m1 m1' ->
    (*local_content_eq ge m1 m1' ->
    local_perm_eq ge m1 m1' ->*)
    match_regset rs1 rs1' ->
    exists rs2' m2',
      exec_instr ge f i rs1' m1' = Next rs2' m2' /\
      Mem.extends m2 m2' /\
      match_regset rs2 rs2' /\
      FP.subset (exec_instr_fp ge f i rs1' m1') (exec_instr_fp ge f i rs1 m1).
Proof.
  intros.
  pose proof H as STEP.
  unfold exec_instr in H. 
  ex_match;inv H;unfold exec_instr,exec_instr_fp.

  all : try(
            match goal with
            |H: exec_load _ _ _ _ _ _ = _ |- _ =>
             eapply exec_load_fp_match in H as ?;eauto;Hsimpl;
             eapply exec_load_match in H as ?;eauto;Hsimpl
            |H: exec_store _ _ _ _ _ _ _= _ |- _ =>
             eapply exec_store_fp_match in H as ?;eauto;
             eapply exec_store_match in H as ?;Hsimpl
            end;Esimpl;eauto;fail).
  all : try (Esimpl;eauto;try apply FP.subset_refl;solv_regset;
             match goal with
               |- forall a b:val,_ => intros [][][];subst;simpl;auto
             end;discriminate;fail).

  
  Focus 27.
  {
    eapply Mem.loadv_extends in Hx0 as ?;eauto;Hsimpl.
    eapply Mem.loadv_extends in Hx1 as ?;eauto;Hsimpl.
    eapply Mem.free_parallel_extends in Hx3 as ?;eauto;Hsimpl.
    assert(rs1' RSP = Vptr b i0). solv_rs.
    rewrite H7,H,H3,H5,Hx2.
    Esimpl;eauto. solv_regset. apply FP.subset_refl.
  }
  Unfocus.
  all : try solv_rs;try solv_eq;try solv_rs;try solv_eq;try solv_rs;try solv_eq;try solv_rs;try solv_eq;try discriminate.

  all : try (Esimpl;eauto;try ex_match;check;fail).
  all : eval_check.
  12,13,14,15: unfold goto_label in *;ex_match;try (solv_rs;fail); try solv_eq; try solv_rs; check.
  13 : unfold goto_label in *;ex_match;eapply regset_jmptbl in H1 as ?;eauto;try solv_eq;solv_eq;check.
  all : try (ex_match;check;fail).

  Focus 10.
  {
    Esimpl;eauto;try apply FP.subset_refl;  solv_regset;auto.
    solv_regset.
    apply compare_floats32_regset_match;solv_regset;auto.
    apply compare_floats32_regset_match;solv_regset;auto.
  }
  Unfocus.
  Focus 10.
  {
    eapply Mem.alloc_extends with(lo2:=0)(hi2:=sz) in Hx0 as ?;eauto;try Lia.lia;Hsimpl; rewrite H.
    eapply Mem.storev_extends in Hx1 as R1;eauto;Hsimpl.
    eapply Mem.storev_extends in Hx2 as R2;eauto;Hsimpl.

    rewrite H3,H5.
    Esimpl;eauto. solv_regset.
    try apply FP.subset_parallel_union;try apply FP.subset_refl.
    revert H0;clear;intros.
    unfold MemOpFP.alloc_fp. unfold FMemOpFP.uncheck_alloc_fp.
    apply Mem.mext_next in H0;eauto.
    rewrite H0. apply FP.subset_refl.
  }
  Unfocus.
  all :try (erewrite check_vundef_lessdef;try apply Hx0;solv_regset;auto).
  Focus 9.
  Esimpl;eauto;try apply FP.subset_refl.
  solv_regset;eapply compare_floats_regset_match;solv_regset;eauto.
  
  { Esimpl; eauto; try solv_regset; try erewrite extends_check_compare_ints_match; eauto;
      solv_regset;
      eauto using extends_compare_ints_regset_match,
      extends_compare_ints_fp_match. }
  { Esimpl; eauto; try solv_regset;
      eauto using extends_compare_longs_regset_match, extends_compare_longs_fp_match. }
  { pose proof (H1 r1) as A. cut (Val.lessdef (Vint n) (Vint n)). intro B.
    Esimpl; eauto; try solv_regset.
    erewrite extends_check_compare_ints_match; eauto. 
    solv_regset; eauto using extends_compare_ints_regset_match.
    eauto using extends_compare_ints_fp_match. auto. }
  { Esimpl; eauto; try solv_regset;
      eauto using extends_compare_longs_regset_match, extends_compare_longs_fp_match. }

  all : destruct (rs1 r1) eqn:?;try discriminate.
  all : eapply match_regset_rs_val2 in Heqv as Heqv2;try apply H1;eauto;try discriminate.
  all: try destruct (rs1 r2) eqn:?;try discriminate.
  all : try (eapply match_regset_rs_val2 in Heqv0 as Heqv3;try apply H1;eauto;try discriminate).
    
  all : unfold Val.and,Val.andl in *;simpl in *;solv_eq;try solv_eq.
  all: unfold compare_ints,compare_ints_fp,compare_longs,compare_longs_fp in *;simpl in *.
  all :Esimpl;eauto;try apply FP.subset_refl.
  all: solv_regset.
Qed.
Lemma extcall_arg_match:
  forall rs m ef args fp rs' m',
    match_regset rs rs'->
    Mem.extends m m'->
    extcall_arg rs m ef args ->
    extcall_arg_fp rs ef fp ->
    exists args0 ,
      Val.lessdef args args0 /\
      extcall_arg rs' m' ef args0 /\
      extcall_arg_fp rs' ef fp.
Proof.
  intros.
  inv H2;inv H1.
  Esimpl;eauto. 
  econstructor. constructor.

  assert(rs RSP <> Vundef). intro.
  rewrite H1 in H6. inv H6.
  assert(Val.lessdef (rs RSP)(rs' RSP)). solv_regset;auto.
  inv H2;try congruence.
  
  Hsimpl. rewrite H5 in*.
  eapply Mem.loadv_extends in H6;eauto.
  Hsimpl.
  Esimpl;eauto.  econstructor;eauto.
  econstructor;eauto.
Qed.
Lemma extcall_arg_pair_match:
  forall rs m ef args fp rs' m',
    match_regset rs rs'->
    Mem.extends m m'->
    extcall_arg_pair rs m ef args ->
    extcall_arg_pair_fp rs ef fp ->
    exists args0,
      Val.lessdef args args0 /\
      extcall_arg_pair rs' m' ef args0 /\
      extcall_arg_pair_fp rs' ef fp.
Proof.
  intros.
  inv H1;inv H2.
  eapply extcall_arg_match in H3;eauto;Hsimpl;Esimpl;eauto;constructor;auto.

  eapply extcall_arg_match in H3 as ?;eauto.
  eapply extcall_arg_match in H4 as ?;eauto.
  Hsimpl.
  exists (Val.longofwords x0 x).
  
  Esimpl;eauto. solv_regset.
  intros [] [] [] ;auto;congruence.
  econstructor;eauto.
  econstructor;eauto.
Qed.
Lemma extcall_arguments_match:
  forall rs m ef args fp rs' m',
    match_regset rs rs'->
    Mem.extends m m'->
    extcall_arguments rs m ef args ->
    extcall_arguments_fp rs ef fp ->
    exists args0,
      Val.lessdef_list args args0 /\
      extcall_arguments rs' m' ef args0 /\
      extcall_arguments_fp rs' ef fp.
Proof.
  unfold extcall_arguments.
  unfold extcall_arguments_fp.
  intros.
  generalize dependent fp.
  induction H1;intros. inv H2.
  Esimpl;eauto.  constructor. constructor.
  inv H3.
  eapply IHlist_forall2 in H7.
  Hsimpl.
  eapply extcall_arg_pair_match in H6 as ?;eauto.
  Hsimpl.
  Esimpl;eauto; econstructor;eauto.
Qed.

Require Import loadframe.
Lemma store_args_mem_extends:
  forall args m m' stk tys m1 ,
    store_args m stk args tys = Some m1 ->
    Mem.extends m m' ->
    exists m1', store_args m' stk args tys = Some m1' /\ Mem.extends m1 m1'.
Proof.
  unfold store_args in *.
  intro args.
  generalize 0.
  induction args.
  intros. simpl in *.
  ex_match. Esimpl;eauto. congruence.

  intros.
  simpl in *.
  ex_match;try solv_eq.
  all : unfold store_stack,Mach.store_stack in *.
  all : try (eapply Mem.storev_extends in Hx1 as ?;eauto;Hsimpl;try solv_eq;eapply IHargs in H as ?;try apply H;eauto;fail).

  eapply Mem.storev_extends in Hx2 as ?;eauto;Hsimpl;solv_eq.
  eapply Mem.storev_extends in Hx3 as ?;eauto;Hsimpl;solv_eq.
  eapply IHargs in H as ?;eauto.

  eapply Mem.storev_extends in Hx2 as ?;eauto;Hsimpl;solv_eq.
  eapply Mem.storev_extends in Hx3 as ?;eauto;Hsimpl;solv_eq.
  eapply Mem.storev_extends in Hx2 as ?;eauto;Hsimpl;solv_eq.
Qed.  
Lemma store_args_validity_preserve:
  forall b m a c m' t,
    Mem.valid_block m t->
    store_args m a b c = Some m'->
    Mem.valid_block m' t.
Proof.
  unfold store_args.
  intro.
  generalize 0.
  induction b.
  intros. simpl in H0. ex_match.
  intros.
  simpl in H0.
  ex_match.
  all :unfold store_stack,Mach.store_stack,Mem.storev in *;ex_match.
  all: try eapply Mem.store_valid_block_1 in Hx1;eauto.
  eapply IHb in H0;eauto.
  do 2 (eapply Mem.store_valid_block_1;eauto).
Qed.
Lemma range_locset_expend1_subset:
  forall b i ,
    Locs.subset (FMemOpFP.range_locset b i 1)(FMemOpFP.range_locset b (i - 1)2).
Proof.
  unfold FMemOpFP.range_locset.
  Locs.unfolds.
  intros.
  ex_match.
  subst.
  destruct zle,zlt,zle,zlt;auto;try Lia.lia.
Qed.
Ltac invMS :=
  match goal with
  | H: MS _ _ _ _ _ _ ?cm1 ?cm2 |- _ =>
    destruct cm1 as [sc Hm]; destruct cm2 as [tc Lm];
    unfold MS in H; simpl in H;
    destruct H as [MC [FPMATCH [SVALID [TVALID [AGMU RCPRESV]]]]]
  | H: MS _ _ _ _ _ _ ?cm1 ?cm2 |- _ =>
    unfold MS in H; simpl in H;
    destruct H as [MC [FPMATCH [SVALID [TVALID [AGMU RCPRESV]]]]]
  end.
Lemma cmpu_bool_some_eq:
  forall m m' rs rs' i j b k,
    Mem.extends m m'->
    match_regset rs rs'->
    Val.lessdef i k->
    Val.cmpu_bool (Mem.valid_pointer m) Ceq i (rs j) = Some b->
    Val.cmpu_bool (Mem.valid_pointer m') Ceq k (rs' j) = Some b.
Proof.
  intros.
  assert(rs j <> Vundef).
  intro. rewrite H3 in *.
  compute in H2. ex_match.
  assert(Val.lessdef (rs j)(rs' j)).
  solv_regset;auto.
  inv H4;try congruence.
  inv H1;[|inv H2].
  assert(forall m m' b i j,
            Mem.valid_pointer m b i || Mem.valid_pointer m b j = true->
            (forall b i ,Mem.valid_pointer m b i = true -> Mem.valid_pointer m' b i = true) ->
            Mem.valid_pointer m' b i||Mem.valid_pointer m' b j = true).
  clear.
  intros.
  destruct Mem.valid_pointer eqn:?;simpl in *;eauto with bool.
  assert(forall b i,Mem.valid_pointer m b i = true->Mem.valid_pointer m' b i = true).
  intros;eauto.
  eapply Mem.valid_pointer_extends ;eauto.
  unfold Val.cmpu_bool in *.
  ex_match;try solv_rs;try solv_eq.
  destruct Int.eq;simpl in *.
  eapply H1 in Hx2;eauto.
  congruence.
  congruence.
  destruct Int.eq;simpl in *;try congruence.
  eapply H1 in Hx2;eauto. congruence.
  destruct ((Mem.valid_pointer m b1 (Ptrofs.unsigned i)) || (Mem.valid_pointer m b1 (Ptrofs.unsigned i - 1))) eqn:?;simpl in *;try congruence.
  eapply H1 in Hx3;eauto.
  eapply H1 in Heqb0;eauto.
  rewrite Hx3,Heqb0 in Hx4;inv Hx4.
  destruct (Mem.valid_pointer) eqn:?;simpl in *;try congruence.
  eapply Mem.valid_pointer_extends in Heqb2;eauto.
  eapply Mem.valid_pointer_extends in Hx3;eauto.
  rewrite Heqb2,Hx3 in Hx4;simpl in *;congruence.
Qed.

Require Import AsmLocalize.
Theorem id_trans_asm_correct: seq_correct id_trans_asm.
Proof.
  unfold seq_correct. intros. unfold id_trans_asm in H. monadInv H.
  split; auto.
  eapply localize; simpl.
  exact asm_localize. exact asm_lift.
  intros. destruct H.
  eapply nodup_gd_init_genv_ident_exists; eauto. inv H0. auto.
  intros. destruct H.
  eapply nodup_gd_init_genv_ident_exists; eauto. inv H0. auto.
  split; auto. split; auto.
  intros ? ? ? ? ? ? ? ; simpl in *.
  inv H; inv H0. inv H3; inv H2. simpl in *. subst. rename bound0 into bound.
  remember (Genv.globalenv (mkprogram (cu_defs tu) (cu_public tu) 1%positive)) as ge0 eqn:G0.
  assert (GEBOUND0 = GEBOUND) by apply Axioms.proof_irr. subst GEBOUND0.
  remember (ge_extend ge0 bound GEBOUND) as ge eqn:G.
  eapply (Local_ldsim _ _ _ _ nat lt).
  
  instantiate(1:= MS ge).
  econstructor;eauto;simpl;try (intros;invMS;destruct AGMU;auto;fail).
  apply lt_wf.
  
  constructor; try tauto. intros. rewrite H in H0. inversion H0. subst b'.
  simpl. destruct (Maps.PTree.get b (Genv.genv_defs ge)); try constructor.
  destruct g; try constructor. destruct v; try constructor.
  (*init*)
  {
    intros. unfold init_core, fundef_init in *.
    destruct (Genv.find_symbol ge id); try discriminate.
    destruct (Genv.find_funct_ptr ge b); try discriminate.
    destruct f; try discriminate.
    destruct (wd_args argSrc (sig_args (fn_sig f))) eqn:WDARG; try discriminate.
    erewrite wd_args_inject; eauto. inversion H3. clear H3. subst score.
    eexists. split. eauto. intros sm tm INITSM INITTM MEMREL sm' tm' HLRELY.
    exists 0%nat. 
    assert (argSrc = argTgt).
    { revert argTgt MEMREL H1 H2. clear.
        induction argSrc; intros; inv H1; inv H2; auto.
        f_equal; auto. inv H1; auto; try contradiction.
        unfold Bset.inj_to_meminj in H. destruct (inj mu b1) eqn:INJ; try discriminate.
        inv H. exploit inj_inject_id; eauto. unfold Bset.inj_to_meminj. rewrite INJ. eauto.
        intro A; inv A. rewrite Ptrofs.add_zero. auto. }
    subst argTgt. rename argSrc into args.
    { destruct HLRELY as [HRELY LRELY INV]. constructor. constructor; auto.
      assert (Mem.extends sm tm).
      { generalize MEMREL H. clear; intros ? GE_INIT_INJ.
          destruct MEMREL. eapply inject_implies_extends; eauto.
          intros. unfold Mem.valid_block in H; rewrite <- dom_eq_src in H.
          eapply Bset.inj_dom in H; eauto.
          destruct H as [b' A]. unfold Bset.inj_to_meminj. rewrite A. eauto.
          inv GE_INIT_INJ.
          rewrite mu_shared_src in dom_eq_src.
          rewrite mu_shared_tgt in dom_eq_tgt.
          assert (forall b, Plt b (Mem.nextblock sm) <-> Plt b (Mem.nextblock tm)).
          { intro. rewrite <- dom_eq_src, <- dom_eq_tgt. tauto. }
          destruct (Pos.lt_total (Mem.nextblock sm) (Mem.nextblock tm)) as [LT | [EQ | LT]]; auto;
            generalize H LT; clear; intros; exfalso;
              apply H in LT; eapply Pos.lt_irrefl; eauto. }
      eapply extends_rely_extends; eauto. inv MEMREL; eauto.
      constructor; auto.
      Esimpl. eresolvfp.
      
      4:  apply MemClosures_local.reach_closed_unmapped_closed;inv LRELY; auto.
      
      {
        intros.
        unfold Mem.valid_block.
        destruct INITSM,HRELY.
        rewrite EQNEXT,<-dom_match.
        inv H. simpl in *. rewrite mu_shared_src in H3.
        auto.
      }
      {
        intros;unfold Mem.valid_block;destruct INITTM,LRELY.
        rewrite EQNEXT,<-dom_match. inv H;simpl in *.
        rewrite mu_shared_tgt in H3;auto.
        }
      inversion H; inversion MEMREL. constructor; auto.
      unfold sep_inject. intros. 
      unfold Bset.inj_to_meminj in *. destruct (Injections.inj mu b0) eqn:?; [|inv H3].
      eapply Bset.inj_range' in Heqo;[|inv mu_inject; eauto]. inv H3. inv H4.
      rewrite mu_shared_tgt, <- mu_shared_src in Heqo.
      eapply Bset.inj_dom in Heqo; eauto. destruct Heqo.
      rewrite H3. exploit inj_inject_id. rewrite H3. eauto. intro C. inv C; auto.
      
    }
  }
  (* step *)
  {
    intros until Hm'.
    right. exists 0%nat. clear G0 G. pose proof H0 as STEP0.
    inv H0.
    (* exec instr *)
    {
      invMS;intros;simpl in *.
      inversion MC. subst rs0 lf0 Hm Lm Lcore.
      eapply exec_instr_match in H4 as STEP;eauto.
      Hsimpl;Esimpl;eauto.
      constructor.  econstructor;eauto.
      solv_rs.
      eresolvfp.
      unfold MS;Esimpl;eauto.
      econstructor;eauto; eresolvfp.
      eresolvfp.
      eapply exec_instr_valid_block;eauto.
      eapply exec_instr_valid_block2;eauto.
      {
        unfold exec_instr in *.
        
        ex_match;repeat solv_eq.
        all: unfold exec_load,exec_store,Mem.storev,goto_label in *;repeat ex_match;repeat solv_eq;try (resvalid;auto;fail).
        all : try (eapply eval_addrmode_lessdef with(ge:= ge)(a:=a) in H5;inv H5;repeat solv_eq;resvalid;fail).
        {
          assert(b1 = b0). Local Transparent Mem.alloc.
          inv H9. unfold Mem.alloc in *.
          try congruence.
          subst. solv_eq. solv_eq. 
          assert(unmapped_closed mu m3 m0). resvalid.
          assert(forall b : block, Bset.belongsto (SharedSrc mu) b -> Mem.valid_block m3 b). resvalid.
          assert(forall b : block, Bset.belongsto (SharedTgt mu) b -> Mem.valid_block m0 b). resvalid.
          assert(unmapped_closed mu m4 m1). resvalid.
          assert(forall b : block, Bset.belongsto (SharedSrc mu) b -> Mem.valid_block m4 b). resvalid.
          assert(forall b : block, Bset.belongsto (SharedTgt mu) b -> Mem.valid_block m1 b). resvalid.
          resvalid.
        }
        {
          solv_rs.
          resvalid.
        }
      }
    }
    {
      invMS;intros;simpl in *.
      inversion MC. subst rs0 lf0 Hm' Lm Lcore.
      exploit (@eval_builtin_args_lessdef _ ge (fun r => rs#r) (fun r => rs'#r)); eauto.
      intros (vargs' & P & Q).
      
      exploit (MemOpFP.eval_builtin_args_fp_lessdef _ ge (fun r => rs#r) (fun r => rs'#r)); eauto.
      intros EVALFP.
      exploit external_call_mem_extends; eauto.
      intros [v' [m'1 [A [B [C D]]]]].
      pose proof A as A'. apply helpers.i64ext_effects in A'.
      destruct A'; subst m'1 .
      assert(rs' RSP = rs RSP).
      assert(Val.lessdef (rs RSP)(rs' RSP)). solv_regset;auto.
      inv H;auto. rewrite H11 in *. contradiction.
      Esimpl;auto. constructor;auto. econstructor 2;eauto.
      solv_rs;auto.
      intro. solv_rs.
      rewrite H;eauto.
      rewrite H;eauto.
      eresolvfp.
      unfold MS. Esimpl;eauto;try resolvfp.
      constructor;eauto.
      subst.
      unfold nextinstr_nf.
      solv_regset.
      auto.
    }
    {
      invMS;intros;simpl in *.
      inv MC.
      eapply extcall_arguments_match in H3 as ?;eauto.
      Hsimpl.
      Esimpl;eauto. constructor. econstructor 3;eauto.
      solv_rs.
      eresolvfp.
      unfold MS.
      Esimpl;eauto;try eresolvfp;try resvalid.
      econstructor 3;eauto.
    }
    {
      invMS;intros;simpl in *.
      inversion MC;Hsimpl.
      subst Lcore ef0 args0 rs0 lf0 Hm' Lm.
      eapply external_call_mem_extends in H4;eauto.
      Hsimpl.
      apply helpers.i64ext_effects in H as ?;Hsimpl;subst.
      Esimpl;eauto.
      constructor. econstructor;eauto.
      solv_rs.
      eapply helpers.i64ext_extcall_forall in H;eauto.
      eresolvfp.
      unfold MS.
      Esimpl;eauto;try eresolvfp;try resvalid.
      econstructor;eauto.
      solv_regset.
      unfold set_pair. ex_match;solv_regset.
      auto.
    }
    {
      invMS. intros.
      inversion MC. subst fb0 args tys0 retty0 Hm Lm Lcore.
      eapply Mem.alloc_extends with(lo2:=0)(hi2:=(4*z)) in H2 as ?;eauto;try Lia.lia.
      Hsimpl.

      assert((MemOpFP.alloc_fp m 0 (4*z))=(MemOpFP.alloc_fp m' 0 (4*z))).
      revert H0;clear.
      intros.
      unfold MemOpFP.alloc_fp,FMemOpFP.uncheck_alloc_fp.
      inv H0. rewrite mext_next. auto. 
      eapply store_args_mem_extends in H4 as ?;eauto.
      Hsimpl.
      Esimpl;eauto. constructor.
      econstructor;eauto.
      eresolvfp. rewrite H5. eresolvfp.
      unfold MS.
      rewrite H5.
      assert(forall b, Bset.belongsto(SharedSrc mu) b -> Mem.valid_block m1 b).
      resvalid.
      assert(forall b, Bset.belongsto(SharedTgt mu) b -> Mem.valid_block x b).
      resvalid.
      Esimpl;eauto;try eresolvfp;try resvalid.
      constructor;auto.
      subst rs0. solv_regset. constructor.
      intros. apply H8 in H10;eapply store_args_validity_preserve;eauto.
      intros. apply H9 in H10. eapply store_args_validity_preserve;eauto.
      assert(unmapped_closed mu m1 x).
      clear H8 H9.
      resvalid.

      revert H4 H6 H8 H9 H10 AGMU.
      clear.
      unfold store_args.
      generalize 0.
      revert Hm' x0 m1 x tys.
      induction args0.
      intros. simpl in *. ex_match.
      intros. simpl in *.
      ex_match.
      all: unfold store_stack,Mach.store_stack,Mem.storev in *;ex_match.
      all: try(assert(unmapped_closed mu m0 m);[resvalid|];assert(forall b, Bset.belongsto (SharedSrc mu) b -> Mem.valid_block m0 b);[resvalid|];assert(forall b, Bset.belongsto (SharedTgt mu) b -> Mem.valid_block m b);[resvalid|];try (eapply IHargs0 in H6;eauto;fail)).
      assert(unmapped_closed mu m2 m);[resvalid|];assert(forall b, Bset.belongsto (SharedSrc mu) b -> Mem.valid_block m2 b);[resvalid|];assert(forall b, Bset.belongsto (SharedTgt mu) b -> Mem.valid_block m b);[resvalid|].
      assert(unmapped_closed mu m3 m0);[resvalid|];assert(forall b, Bset.belongsto (SharedSrc mu) b -> Mem.valid_block m3 b);[resvalid|];assert(forall b, Bset.belongsto (SharedTgt mu) b -> Mem.valid_block m0 b);[resvalid|].
      eapply IHargs0 in H6;eauto.
    }
    (*
    {
      invMS.
      inv MC.
      Esimpl;eauto.
      constructor.
      eapply exec_step_to_lock;eauto.
      solv_rs.
      eresolvfp.

      unfold MS;Esimpl;eauto;try eresolvfp;try resvalid.
      constructor;auto.
    }
    {
     
      invMS.
      inv MC.
      
      assert(exists rs'' Lm',exec_locked_instr ge i0 rs'0 Lm = Next rs'' Lm' /\
                        FP.subset  (exec_locked_instr_fp ge i0 rs'0 Lm) (exec_locked_instr_fp ge i0 rs Hm) /\ Mem.extends Hm' Lm' /\ match_regset rs' rs'').
      {
        unfold exec_locked_instr,exec_locked_instr_fp in *|-.
        ex_match;try (solv_eq;fail).
        eapply exec_load_fp_match in H4 as ?;eauto;eapply exec_load_match in H4 as ?;eauto;Hsimpl;Esimpl;eauto.

        eapply Mem.loadv_extends in Hx0 as ?;eauto.
        eapply Mem.storev_extends in Hx1 as ?;eauto.
        Hsimpl.
        eapply eval_addrmode_lessdef in H10 as ?.
        inv H8. rewrite H12 in H,H0.
        Esimpl;eauto.
        unfold exec_locked_instr.
        rewrite H,H0. eauto.
        unfold exec_locked_instr_fp. 
        rewrite H12. apply FP.subset_refl. inv H4. auto.
        inv H4. solv_regset.
        rewrite <- H11 in H. inv H.
        
        
        eapply Mem.storev_extends in Hx3 as ?;eauto;Hsimpl.
        eapply eval_addrmode_lessdef in H10 as ?.
        inv H6. rewrite H9 in H.
        
        eapply Mem.loadv_extends in Hx0 as ?;eauto;Hsimpl.
        
        unfold exec_locked_instr.
        rewrite H,<-H9,H6.

        assert(Val.cmpu_bool (Mem.valid_pointer Lm) Ceq x0 (rs'0 RAX) = Some true).
        {
          revert Hx1 H5 H10 H7.
          clear.
     
          intros.
          assert(rs RAX <> Vundef).
          intro. rewrite H in Hx1.
          compute in Hx1. ex_match.
          assert(Val.lessdef (rs RAX)(rs'0 RAX)).
          solv_regset;auto.
          inv H0;try congruence.
          inv H7;[|inv Hx1].
          unfold Val.cmpu_bool in *.
          ex_match;try solv_rs;try solv_eq.
          {
            revert Hx4 Hx5 H5;clear;intros.
            destruct (Mem.valid_pointer Hm b0 (Ptrofs.unsigned i)|| Mem.valid_pointer Hm b0 (Ptrofs.unsigned i - 1)) eqn:?;try discriminate.
            simpl in Hx4.
            pose Mem.valid_pointer_extends.
            assert(forall m m' b i j,
                      Mem.valid_pointer m b i || Mem.valid_pointer m b j = true->
                      (forall b i ,Mem.valid_pointer m b i = true -> Mem.valid_pointer m' b i = true) ->
                      Mem.valid_pointer m' b i||Mem.valid_pointer m' b j = true).
            clear.
            intros.
            destruct Mem.valid_pointer eqn:?;simpl in *;eauto with bool.
            assert(forall b i,Mem.valid_pointer Hm b i = true->Mem.valid_pointer Lm b i = true).
            intros;eauto.
            eapply H in Heqb;eauto.
            eapply H in Hx4;eauto. rewrite Heqb,Hx4 in Hx5. inv Hx5.
          }
        }
        rewrite H8.
        inv H4.
        
        Esimpl;eauto;try resvalid;try solv_regset.
        unfold exec_locked_instr_fp.
        rewrite H9 in *.
        repeat match goal with H: ?P = _|- context[match ?P with _ => _ end] => rewrite H end.
        do 2 (eapply FP.subset_parallel_union;try apply FP.subset_refl).
        {
          revert Hx1 H5 H10 H7.
          revert H8.
          clear.
          intros.
          assert(rs RAX <> Vundef).
          intro. rewrite H in Hx1.
          compute in Hx1. ex_match.
          assert(Val.lessdef (rs RAX)(rs'0 RAX)).
          solv_regset;auto.
          inv H0;try congruence.
          inv H7;[|inv Hx1].
          unfold Val.cmpu_bool,ValFP.cmpu_bool_fp_total in *.
          ex_match;try solv_rs;try solv_eq.
          apply FP.subset_refl.
          assert(forall b i m m',
                    Mem.extends m m'->
                    FP.subset (MemOpFP.weak_valid_pointer_fp m' b i)(MemOpFP.weak_valid_pointer_fp m b i)).
          clear.
          intros.
          unfold MemOpFP.weak_valid_pointer_fp.
          ex_match;try apply FP.subset_refl.
          unfold FMemOpFP.valid_pointer_fp.
          constructor;try apply range_locset_expend1_subset;try apply Locs.subset_refl.
          eapply Mem.valid_pointer_extends in H;eauto;congruence.

          eapply FP.subset_parallel_union;eauto.
        }

        solv_eq.
        rewrite <- H8 in *. simpl in H. congruence.

        eapply Mem.loadv_extends in Hx0 as ?;eauto.
        Hsimpl.
        eapply eval_addrmode_lessdef in H10 as ?.
        inv H6.
        unfold exec_locked_instr,exec_locked_instr_fp.
        rewrite H9 in *. rewrite H,Hx0.
        
        assert(Val.cmpu_bool (Mem.valid_pointer Lm) Ceq x (rs'0 RAX) = Some false).
        eapply cmpu_bool_some_eq;eauto.
        rewrite H6,Hx1.
        inv H4.
        Esimpl;eauto;try resvalid;try solv_regset.
        eapply FP.subset_parallel_union;eauto;try apply FP.subset_refl.
        {
          revert Hx1 H5 H10 H0.
          revert H6.
          clear.
          intros.
          assert(rs RAX <> Vundef).
          intro. rewrite H in Hx1.
          compute in Hx1. ex_match.
          assert(Val.lessdef (rs RAX)(rs'0 RAX)).
          solv_regset;auto.
          inv H1;try congruence.
          inv H0;[|inv Hx1].
          unfold Val.cmpu_bool,ValFP.cmpu_bool_fp_total in *.
          assert(forall b i m m',
                    Mem.extends m m'->
                    FP.subset (MemOpFP.weak_valid_pointer_fp m' b i)(MemOpFP.weak_valid_pointer_fp m b i)).
           clear.
          intros.
          unfold MemOpFP.weak_valid_pointer_fp.
          ex_match;try apply FP.subset_refl.
          unfold FMemOpFP.valid_pointer_fp.
          constructor;try apply range_locset_expend1_subset;try apply Locs.subset_refl.
          eapply Mem.valid_pointer_extends in H;eauto;congruence.
          
          ex_match;try solv_rs;try solv_eq;try apply FP.subset_refl.
          eapply FP.subset_parallel_union;eauto.
        }
        rewrite <- H8 in H. inv H.
      }
      Hsimpl.
      Esimpl;eauto.
      constructor. 
      eapply exec_step_locked;eauto.
      solv_rs.
      resolvfp.
      unfold MS.
      Esimpl;eauto;try eresolvfp;try resvalid.
      econstructor;eauto.
      eapply exec_locked_instr_valid_block;eauto.
      eapply exec_locked_instr_valid_block2;eauto.
      {
        unfold exec_locked_instr in *.
        destruct i0 eqn:?;simpl in *;try congruence.
        unfold exec_load in *;repeat ex_match;repeat solv_eq;try (resvalid;auto;fail).
        {
          ex_match.
          inv H. inv H4.
          unfold Mem.storev in *.
          ex_match.
          eapply eval_addrmode_lessdef in H10;eauto.
          inv H10. rewrite<- H8 in Hx3. rewrite Hx3 in Hx4;inv Hx4.
          resvalid.
          rewrite <- H4 in Hx4. inv Hx4.
        }
        {
          ex_match.
          solv_eq.
          unfold Mem.storev in *;ex_match.
          eapply eval_addrmode_lessdef in H10;eauto.
          inv H10. rewrite<- H9 in Hx1. rewrite Hx1 in Hx5;inv Hx5.
          resvalid. solv_eq. inv H4. resvalid.
          rewrite <- H8 in Hx5. inv Hx5.
          pose proof cmpu_bool_some_eq.
          exfalso.
          
          eapply cmpu_bool_some_eq in Hx4 as ?.
          rewrite Hx0 in H9.
          congruence.
          auto. auto.
          revert H5 Hx3 Hx H10;clear;intros.
          unfold Mem.loadv in *.
          ex_match.
          eapply eval_addrmode_lessdef in H10 as ?.
          inv H. rewrite H2,Hx0 in Hx1. inv Hx1. 
          eapply Mem.load_extends in H5;eauto.
          Hsimpl. solv_eq. auto.
          rewrite <- H1 in Hx1. inv Hx1.

          solv_eq.
          inv H4.

          eapply cmpu_bool_some_eq in Hx3 as ?.
          rewrite H in Hx0. inv Hx0.
          auto.
          auto.

          revert Hx Hx2 H5 H10. clear;intros.
          unfold Mem.loadv in *;ex_match.
          eapply eval_addrmode_lessdef in H10 as ?.
          inv H. rewrite<- H2,Hx0 in Hx1. inv Hx1.
          eapply Mem.load_extends in H5;eauto;Hsimpl;solv_eq;auto.
          rewrite<- H1 in *;simpl in *;congruence.
        }
      }
    } *)
  }
  (* atext *)
  {
    intros.
    invMS.
    
    inversion MC; subst Hcore Lcore m m';try discriminate.

    unfold at_external in *.
    ex_match. inversion H0;clear H0;subst i0 sg0 args.
    Esimpl;eauto.
    {
      unfold LDSimDefs.arg_rel.
      clear MC.
      revert args' AGMU H2 H8 ; clear.
      (** should be extracted as a lemma ... *)
      induction argSrc; intros args' AGMU GARG LD. simpl. inv LD. auto. inv LD. inv GARG.
      constructor; auto. clear H3 H4 IHargSrc. inv H1; auto. destruct v2; auto.
      simpl in H2. eapply Bset.inj_dom in H2; inv AGMU; eauto.
      destruct H2. exploit proper_mu_inject_incr. unfold Bset.inj_to_meminj; rewrite H; eauto.
      intro. inv H0. econstructor. unfold Bset.inj_to_meminj; rewrite H. eauto. rewrite Ptrofs.add_zero; auto. }
    eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_extends; inv AGMU; eauto.
    eapply extends_reach_closed_implies_inject; inv AGMU; eauto.
    unfold MS.
    Esimpl;eauto;try eresolvfp;try resvalid.
    (*
    {
      unfold at_external in *. ex_match.
      inversion H0;subst f sg argSrc.
      Esimpl;eauto.
      constructor.
      eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_extends; inv AGMU; eauto.
      eapply extends_reach_closed_implies_inject; inv AGMU; eauto.
      unfold MS.
      Esimpl;eauto;try eresolvfp;try resvalid.

      Esimpl;eauto;try eresolvfp;try resvalid.
      constructor.
      eapply MemClosures_local.unmapped_closed_reach_closed_preserved_by_extends; inv AGMU; eauto.
      eapply extends_reach_closed_implies_inject; inv AGMU; eauto.
      unfold MS.
      Esimpl;eauto;try eresolvfp;try resvalid.
    }
    *)
  }
  (* aftext *)
  {
    intros i mu Hcore Hm Lcore Lm oresSrc Hcore' oresTgt MATCH GRES AFTEXT ORESREL.
    simpl in *. unfold after_external in *.

    destruct Hcore;try discriminate.
    {
      destruct f;try discriminate.
      assert(Hcore' =
             match oresSrc with
             | Some res =>  (Core_State (set_pair (loc_external_result sg) res rs) # PC <- (rs RA) loader)
             | None => (Core_State (set_pair (loc_external_result sg) Vundef rs) # PC <-  (rs RA) loader)
             end).
      ex_match.
      invMS. inv MC. 
      exists (match oresTgt with
         | Some res => (Core_State (set_pair (loc_external_result sg) res rs') # PC <- (rs' RA) loader)
         | None =>  (Core_State (set_pair (loc_external_result sg) Vundef rs') # PC <- (rs' RA) loader)
         end).
      Esimpl;eauto.
      ex_match; inv ORESREL;try discriminate;try contradiction;simpl in *;eauto; ex_match.
      intros. exists 1%nat.
      assert (Mem.extends Hm' Lm').
      { inv AGMU; eapply extends_rely_extends; eauto. }
      assert (unmapped_closed mu Hm' Lm').
      { eapply reach_closed_unmapped_closed. inv H. inv H2. auto. }
      destruct oresSrc, oresTgt; try contradiction;ex_match;unfold MS; Esimpl;try eresolvfp;try resvalid; try(econstructor;eauto;solv_regset; unfold set_pair;ex_match;solv_regset; simpl in ORESREL;inv ORESREL;auto;inv AGMU;apply proper_mu_inject_incr in H2; unfold inject_id in H2; inv H2;rewrite MemInterpolant.ptrofs_add_0; auto;fail);try(inv H; inv H2; unfold Mem.valid_block; rewrite EQNEXT; auto;fail);try(inv H; inv H4; unfold Mem.valid_block; rewrite EQNEXT;auto;fail).
    }
    (*
    {
      assert(Hcore' =
             match locked with
             | LOCK =>  (Core_LockState rs STEP loader)
             | _ => (Core_State rs loader)
             end).
      ex_match.
      invMS. inv MC. 
      exists (match locked with
         | LOCK => (Core_LockState rs' STEP loader)
         | _ =>  (Core_State rs' loader)
         end).
      Esimpl;eauto.
      ex_match; inv ORESREL;try discriminate;try contradiction;simpl in *;eauto; ex_match.
      intros. exists 1%nat.
      assert (Mem.extends Hm' Lm').
      { inv AGMU; eapply extends_rely_extends; eauto. }
      assert (unmapped_closed mu Hm' Lm').
      { eapply reach_closed_unmapped_closed. inv H. inv H3. auto. }
      unfold MS.
      Esimpl;eauto;try resolvfp;try resvalid;try(inv H; inv H3; unfold Mem.valid_block; rewrite EQNEXT; auto;fail);try(inv H; inv H4; unfold Mem.valid_block; rewrite EQNEXT;auto;fail).
      ex_match;constructor;auto;try resolvfp;try resvalid.
    }
     *)
  }
  (* halt *)
  {
    intros. simpl in *. unfold halted in *.
    destruct Hcore eqn:?;try discriminate.
    invMS. inv MC.
    destruct l;try discriminate.
    assert (LDefs.Inv mu Hm Lm).
    { inv AGMU. eapply extends_reach_closed_implies_inject; eauto. }
    assert (reach_closed Lm (Injections.SharedTgt mu)).
    { eapply unmapped_closed_reach_closed_preserved_by_injection'; eauto.
      inv AGMU; auto. }


    destruct Val.cmp_bool eqn:?;[|inv H0].
    assert(Val.cmp_bool Ceq (rs' PC) Vzero = Some b).
    revert H4 Heqo;clear;intros.
    unfold Val.cmp_bool in *;simpl in *.
    ex_match;solv_rs;auto.
    rewrite H5.
    
    ex_match.
    {
      Esimpl;eauto.
      inv H0.
      unfold res_rel.
      assert(Val.lessdef (r (preg_of r0))(rs' (preg_of r0))).
      solv_regset;auto.
      inv H0;try constructor.

      
      revert H2 AGMU;clear;intros ? [].
      destruct (r (preg_of r0)).
      all :try constructor.
      unfold inject_incr in proper_mu_inject_incr.
      unfold inject_id in proper_mu_inject_incr.
      simpl in H2. apply proper_mu_inject in H2 as [].
      unfold Bset.inj_to_meminj in proper_mu_inject_incr.
      exploit proper_mu_inject_incr. rewrite H. eauto.
      intro. inv H0.
      rewrite <-Ptrofs.add_zero with(x:=i).
      econstructor;eauto. unfold Bset.inj_to_meminj. rewrite H. eauto.
      do 2 rewrite Ptrofs.add_zero;auto.
    }
    {
      Esimpl;eauto.
      inv H0.
      unfold res_rel.
      assert(Val.lessdef (Val.longofwords(r (preg_of rhi)) (r (preg_of rlo)))(Val.longofwords (rs' (preg_of rhi)) (rs' (preg_of rlo)))).
      solv_regset;auto.
      intros [] [] [] ;auto;congruence.
      inv H0;try constructor.
      revert H2 AGMU;clear;intros ? [].
      destruct (  (Val.longofwords (r (preg_of rhi)) (r (preg_of rlo)))) eqn:?.
      all :try constructor.
      unfold inject_incr in proper_mu_inject_incr.
      unfold inject_id in proper_mu_inject_incr.
      simpl in H2. apply proper_mu_inject in H2 as [].
      unfold Bset.inj_to_meminj in proper_mu_inject_incr.
      exploit proper_mu_inject_incr. rewrite H. eauto.
      intro. inv H0.
      rewrite <-Ptrofs.add_zero with(x:=i).
      econstructor;eauto. unfold Bset.inj_to_meminj. rewrite H. eauto.
      do 2 rewrite Ptrofs.add_zero;auto.
    }
  }
  Unshelve.
  eapply Genv.to_senv;eauto.
  apply Mem.empty.
  apply O.
(*  apply O.
  apply O. *)
Qed.
