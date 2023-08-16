
Require Import Coq.Program.Equality FSets Permutation.
Require Import FSets FSetAVL Orders Mergesort.
Require Import Coqlib Maps Ordered Errors Integers Floats.
Require Intv.
Require Import AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Switch.
Require Import CUAST Footprint Blockset LDSimDefs_local LDSim_local.
Require Import InteractionSemantics IS_local val_casted InjRels
        Op_fp Cminor_op_footprint.

Require Import  Cop Cop_fp_local.
Local Open Scope error_monad_scope.
Local Notation empfp:=FP.emp.
Local Notation footprint:=FP.t.
Ltac inv_eq:=
  repeat match goal with
         | H:?P , H1: ?P |- _ => clear H
         | H: context[match ?x with _ => _ end] |- _ => destruct x eqn:?; inversion H ;subst
         | H:?P = ?Q, H1:context [ ?P ] |- _ => rewrite H in H1
         | H:?P = ?Q |- context [ ?P ] => rewrite H 
         end;
  simpl in *;subst;try contradiction;try discriminate.
Ltac Hsimpl:=
  repeat match goal with
         | H1:?a,H2:?a->?b|-_=>specialize (H2 H1)
         | H:_/\_|-_=> destruct H
         | H:exists _,_|-_=>destruct H
         end.
Ltac Esimpl:=
  repeat match goal with
         | H:_|-_/\_=>split
         | H:_|-exists _,_=>eexists
         end.

Definition in_fp (b:block)(ofs:Z)(fp:footprint):Prop:=
  Locs.belongsto fp.(FP.reads) b ofs \/
  Locs.belongsto fp.(FP.writes) b ofs\/
  Locs.belongsto fp.(FP.cmps) b ofs \/
  Locs.belongsto fp.(FP.frees) b ofs.

Definition in_fps (b:block)(ofs:Z)(fp fp':footprint):Prop:=
  (Locs.belongsto fp'.(FP.reads) b ofs -> Locs.belongsto fp.(FP.reads) b ofs) /\
  (Locs.belongsto fp'.(FP.writes) b ofs  -> Locs.belongsto fp.(FP.writes) b ofs) /\
  (Locs.belongsto fp'.(FP.cmps) b ofs  -> Locs.belongsto fp.(FP.cmps) b ofs) /\
  (Locs.belongsto fp'.(FP.frees) b ofs  -> Locs.belongsto fp.(FP.frees) b ofs).
Lemma in_empfp:
  forall b ofs,
    ~in_fp b ofs empfp.
Proof.
  unfold in_fp;intros.
  intro.
  destruct H as [|[|[|]]];inv H.
Qed.
Lemma in_fp_split:
  forall b ofs fp1 fp2,
    in_fp b ofs (FP.union fp1 fp2)->
    in_fp b ofs fp1 \/ in_fp b ofs fp2.
Proof.
  destruct fp1,fp2; unfold in_fp,Locs.belongsto;simpl;unfold Locs.union; intros.
  destruct H as [|[|[|]]];apply orb_true_iff in H as [];auto.
Qed.
Lemma in_fp_union:
  forall b ofs fp1 fp2,
    in_fp b ofs fp1 ->
    in_fp b ofs (FP.union fp1 fp2).
Proof.
  destruct fp1,fp2;unfold in_fp,Locs.belongsto;simpl;unfold Locs.union;intros.
  destruct H as [|[|[|]]];rewrite H;auto.
Qed.
Lemma in_fps_union:
  forall b ofs fp1 fp1' fp2 fp2',
    in_fps b ofs fp1 fp1' ->
    in_fps b ofs fp2 fp2'->
    in_fps b ofs (FP.union fp1 fp2)(FP.union fp1' fp2').
Proof.
  destruct fp1,fp2;unfold in_fp,Locs.belongsto;simpl;unfold Locs.union;intros.
  unfold in_fps in *;simpl in *.
  Hsimpl;Esimpl;intros;apply belongsto_union in H7 as [];apply belongsto_union;auto.
Qed.
Lemma weak_valid_pointer_block_eq:
  forall b ofs m b' ofs',
    in_fp b ofs (MemOpFP.weak_valid_pointer_fp m b' ofs') ->
    b = b'.
Proof.
  unfold MemOpFP.weak_valid_pointer_fp,in_fp,FMemOpFP.valid_pointer_fp.
  intros;inv_eq;simpl in *;unfold Locs.belongsto,Locs.emp in *;
    destruct H as [|[|[|]]];try discriminate;
      destruct H0 as [|[|]];try discriminate;
        unfold FMemOpFP.range_locset in *;destruct eq_block;try discriminate;auto.
Qed.
Lemma in_fp_subset:
  forall b ofs fp1 fp2,
    in_fp b ofs fp1->
    FP.subset fp1 fp2->
    in_fp b ofs fp2.
Proof.
  destruct fp1,fp2;unfold in_fp,Locs.belongsto;simpl;intros.
  inv H0;simpl in *.
  unfold Locs.subset,Locs.belongsto in *.
  destruct H as [|[|[|]]];eauto.
Qed.
Lemma in_fps_emp:
  forall b ofs fp,
    in_fps b ofs fp empfp.
Proof.
  unfold in_fps;intros;Esimpl;intro;inv H.
Qed.
Definition fp_match bound (fp tfp:footprint):Prop:=
  (forall b ofs,
      Plt b bound->
      in_fps b ofs fp tfp).
Lemma fp_match_union:
  forall ge fp tfp fp2 tfp2,
    fp_match ge fp tfp->
    fp_match ge fp2 tfp2->
    fp_match ge (FP.union fp fp2)(FP.union tfp tfp2).
Proof.
  unfold fp_match;intros.
  eapply in_fps_union;eauto.
Qed.
Lemma weak_valid_pointer_eq:
  forall m b ofs,
    MemOpFP.weak_valid_pointer_fp m b ofs =
    {|
      FP.cmps:= if Mem.valid_pointer m b ofs then FMemOpFP.range_locset b ofs 1 else FMemOpFP.range_locset b (ofs-1) 2 ;
      FP.reads:=Locs.emp;
      FP.writes:=Locs.emp;
      FP.frees:=Locs.emp
    |}.
Proof.
  unfold MemOpFP.weak_valid_pointer_fp,FMemOpFP.valid_pointer_fp;simpl.
  intros. destruct Mem.valid_pointer;auto.
Qed.
Lemma range_locset_belongsto_1:
  forall b ofs ofs',
    Locs.belongsto (FMemOpFP.range_locset b (Ptrofs.unsigned ofs') 1) b ofs->
    Locs.belongsto (FMemOpFP.range_locset b (Ptrofs.unsigned ofs' -1) 2) b ofs.
Proof.
  unfold Locs.belongsto,FMemOpFP.range_locset;intros.
  destruct eq_block;try contradiction.
  apply andb_true_iff in H as [].
  apply andb_true_iff;auto.
  split. destruct zle,zle;try Lia.lia;auto.
  destruct zlt,zlt;try Lia.lia;auto.
Qed.
Lemma cmpu_fp_infps:
  forall ge f m m' c v1 v2 v1' v2' x v
    (DOMAIN: forall b, Plt b ge-> f b = Some (b,0))
    (IMAGE: forall b1 b2 delta,f b1 = Some (b2,delta) -> Plt b2 ge -> b1 = b2),
    Mem.inject f m m'->
    Val.inject f v1 v1'->
    Val.inject f v2 v2'->
    option_map Val.of_bool (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2) =  Some v ->
    option_map Val.of_bool (Val.cmpu_bool (Mem.valid_pointer m') c v1' v2') =Some x ->
    fp_match ge (cmpu_fp m c v1 v2)(cmpu_fp m' c v1' v2').
Proof.
  unfold fp_match,Val.cmpu_bool,cmpu_fp,ValFP.cmpu_bool_fp_total in *;intros.
  inv H0;inv H1;try discriminate;try apply in_fps_emp.
  all: destruct Archi.ptr64 eqn:?;try discriminate.
  {
      destruct Int.eq ;try apply in_fps_emp.
      destruct Val.cmp_different_blocks;try apply in_fps_emp.
      unfold MemOpFP.weak_valid_pointer_fp in *.
      unfold FMemOpFP.valid_pointer_fp in *. clear H2.

      destruct Mem.valid_pointer eqn:?;simpl in *.
      all: unfold in_fps;Esimpl;simpl;intros; try inv H1.
      all: unfold FMemOpFP.range_locset in *  |- .
      all: destruct eq_block;try discriminate;subst b2.
      all: eapply IMAGE in H0 as R;eauto;subst b1.
      all: eapply DOMAIN in H4 as R2;rewrite H0 in R2;inv R2.
      all: rewrite Ptrofs.add_zero in *.
      all: destruct (Mem.valid_pointer m b (Ptrofs.unsigned ofs1)) eqn:?;simpl;unfold FMemOpFP.range_locset,Locs.belongsto;destruct eq_block eqn:?;try contradiction;auto.
      - apply andb_true_iff in H5 as [];apply andb_true_iff;split;auto.
        destruct zle;try discriminate.
        assert(Ptrofs.unsigned ofs1 -1 <= ofs). OmegaPlugin.Lia.lia.
        destruct zle;auto.
        assert(Ptrofs.unsigned ofs1+1 = Ptrofs.unsigned ofs1 -1 +2). Lia.lia.
        rewrite <-H5;auto.
      - eapply Mem.valid_pointer_inject_val in Heqb1;eauto.
        rewrite Ptrofs.add_zero in Heqb1.
        congruence.
  }
  {
    destruct Int.eq ;try apply in_fps_emp.
    destruct Val.cmp_different_blocks;try apply in_fps_emp.
    unfold MemOpFP.weak_valid_pointer_fp in *.
    unfold FMemOpFP.valid_pointer_fp in *. clear H2.
    destruct Mem.valid_pointer eqn:?; unfold in_fps;Esimpl;simpl;intro;inv H0.
    all: unfold FMemOpFP.range_locset in H2;destruct eq_block;try discriminate;subst b2.
    all: eapply IMAGE in H5 as R;eauto;subst b1.
    all: eapply DOMAIN in H4 as R;rewrite H5 in R;inv R.
    all: destruct (Mem.valid_pointer m b (Ptrofs.unsigned ofs1)) eqn:?;simpl.
    all: unfold FMemOpFP.range_locset,Locs.belongsto.
    all: rewrite Ptrofs.add_zero in *;auto.
    all: destruct eq_block eqn:?;try contradiction;auto.

    apply andb_true_iff.
    apply andb_true_iff in H2 as [].
    split.
    destruct zle;try discriminate.
    assert(Ptrofs.unsigned ofs1 -1 <= ofs). OmegaPlugin.Lia.lia.
    destruct zle;auto.
    assert(Ptrofs.unsigned ofs1+1 = Ptrofs.unsigned ofs1 -1 +2). Lia.lia.
    rewrite <-H2;auto.
    
    eapply Mem.valid_pointer_inject_val in Heqb1;eauto.
    rewrite Ptrofs.add_zero in Heqb1.
    rewrite Heqb1 in Heqb3. inv Heqb3.
  }
  {
    rewrite! weak_valid_pointer_eq.
    unfold FP.union;simpl;fold FP.union.
    rewrite Locs.locs_union_emp. clear H2.
    destruct eq_block;[|destruct Val.cmp_different_blocks;try apply in_fps_emp].
    all: unfold in_fps;simpl;Esimpl;intro R;inv R.
      {
        unfold Locs.union in H2.
        assert(b=b3).
        apply orb_true_iff in H2 as [].
        destruct Mem.valid_pointer eqn:?;unfold FMemOpFP.range_locset in H1;destruct eq_block;try discriminate;auto.
        destruct (  Mem.valid_pointer m' b3 (Ptrofs.unsigned (Ptrofs.add ofs0 (Ptrofs.repr delta0)))) eqn:?;unfold FMemOpFP.range_locset in H1;   destruct eq_block;try discriminate;auto.
        
        subst b3.

        exploit DOMAIN;eauto;intro R.
        eapply IMAGE in H0 as ?;eauto;subst b0.
        eapply IMAGE in H5 as ?;eauto;subst b1.
        rewrite R in H0;inv H0;rewrite R in H5;inv H5.
        destruct (eq_block b b) ;try contradiction;simpl.
        rewrite! Ptrofs.add_zero in H2.
        apply belongsto_union.
        apply orb_true_iff in H2.
        destruct H2.
        destruct (Mem.valid_pointer m' b (Ptrofs.unsigned ofs1)) eqn:?.
        left. destruct (Mem.valid_pointer m b (Ptrofs.unsigned ofs1)). auto.
        apply range_locset_belongsto_1;auto.
        left. destruct (Mem.valid_pointer m b (Ptrofs.unsigned ofs1)) eqn:?;auto.
        eapply Mem.valid_pointer_inject_val in Heqb1;eauto.
        rewrite Ptrofs.add_zero in Heqb1;congruence.
        
        destruct (Mem.valid_pointer m' b (Ptrofs.unsigned ofs0)) eqn:?.
        right. destruct (Mem.valid_pointer m b (Ptrofs.unsigned ofs0)). auto.
        apply range_locset_belongsto_1;auto.
        right. destruct (Mem.valid_pointer m b (Ptrofs.unsigned ofs0)) eqn:?;auto.
        eapply Mem.valid_pointer_inject_val in Heqb1;eauto.
        rewrite Ptrofs.add_zero in Heqb1;congruence.
      }
      {
        destruct (eq_block).
        subst b0. rewrite H0 in H5;inv H5. contradiction.
        simpl.
        unfold Locs.union in H2.
        apply orb_true_iff in H2 as []; unfold FMemOpFP.range_locset in H1.
        all: destruct eq_block;try discriminate.
        {
          subst b2.
          eapply IMAGE in H5 as ?;eauto;subst b1.
          exploit DOMAIN;eauto;intro R;rewrite H5 in R;inv R.
          apply belongsto_union;left;auto.
          unfold FMemOpFP.range_locset,Locs.belongsto.
          destruct eq_block;try contradiction.
          rewrite Ptrofs.add_zero in *. auto.
        }
        {
          subst b3.
          eapply IMAGE in H0 as ?;eauto;subst b0.
          exploit DOMAIN;eauto;intro R;rewrite H0 in R;inv R.
          apply belongsto_union;right;auto.
          unfold FMemOpFP.range_locset,Locs.belongsto.
          destruct eq_block;try contradiction.
          rewrite Ptrofs.add_zero in *. auto.
        }
      }
  }
Qed.


Lemma unmapped_closed_alloc_1:
  forall mu Hm Lm Hm' lo hi b
    (SVALID: forall b0 : block,  Bset.belongsto (Injections.SharedSrc mu) b0 -> Mem.valid_block Hm b0)
    (TVALID: forall b0 : block,  Bset.belongsto (Injections.SharedTgt mu) b0 -> Mem.valid_block Lm b0)
    (AGMU: Bset.inject (Injections.inj mu) (Injections.SharedSrc mu) (Injections.SharedTgt mu)),
    MemClosures_local.unmapped_closed mu Hm Lm ->
    Mem.alloc Hm lo hi = (Hm', b)->
    MemClosures_local.unmapped_closed mu Hm' Lm.
Proof.
  intros.
  eapply MemClosures_local.unchanged_on_unmapped_closed_preserved;eauto.
  2: apply Mem.unchanged_on_refl.
  eapply Mem.alloc_unchanged_on;eauto.
Qed.

Lemma unmapped_closed_alloc_2:
  forall mu Hm Lm Lm' lo hi b
    (SVALID: forall b0 : block,  Bset.belongsto (Injections.SharedSrc mu) b0 -> Mem.valid_block Hm b0)
    (TVALID: forall b0 : block,  Bset.belongsto (Injections.SharedTgt mu) b0 -> Mem.valid_block Lm b0)
    (AGMU: Bset.inject (Injections.inj mu) (Injections.SharedSrc mu) (Injections.SharedTgt mu)),
    MemClosures_local.unmapped_closed mu Hm Lm ->
    Mem.alloc Lm lo hi = (Lm', b)->
    MemClosures_local.unmapped_closed mu Hm Lm'.
Proof.
  intros.
  eapply MemClosures_local.unchanged_on_unmapped_closed_preserved;eauto.
  apply Mem.unchanged_on_refl.
  eapply Mem.alloc_unchanged_on;eauto.
Qed.

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
(*
Lemma unmapped_closed_alloc_variables:
  forall vars e e2 mu Hm Lm Hm' 
    (SVALID: forall b0 : block,  Bset.belongsto (Injections.SharedSrc mu) b0 -> Mem.valid_block Hm b0)
    (TVALID: forall b0 : block,  Bset.belongsto (Injections.SharedTgt mu) b0 -> Mem.valid_block Lm b0)
    (AGMU: Bset.inject (Injections.inj mu) (Injections.SharedSrc mu) (Injections.SharedTgt mu)),
    MemClosures_local.unmapped_closed mu Hm Lm ->
    alloc_variables e Hm vars e2 Hm' ->
    MemClosures_local.unmapped_closed mu Hm' Lm.
Proof.
  induction vars;intros.
  inv H0. auto.
  inv H0.
  assert(SVALID': forall b, Bset.belongsto (Injections.SharedSrc mu) b-> Mem.valid_block m1 b).
  resvalid.
  eapply unmapped_closed_alloc_1 in H5;eauto.
Qed.
*)
Lemma freelist_free_unmapped_closed:
  forall F1 V1 F2 V2 mu (ge:Genv.t F1 V1)(tge:Genv.t F2 V2) Lm f0 sp l (m m' x : mem) tfn (z : Z),
    Mem.free_list m l = Some m' ->
    Mem.free Lm sp z tfn = Some x ->
    proper_mu ge tge f0 mu ->
    (forall b : block,
        Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block m b) ->
    (forall b : block,
        Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block Lm b) ->
    ~ Plt sp (Genv.genv_next ge) ->
    Genv.genv_next ge = Genv.genv_next tge ->
    MemClosures_local.unmapped_closed mu m Lm ->
    (forall (b : block) (lo hi : Z),
        In (b, lo, hi) l -> ~ Plt b (Genv.genv_next ge) /\ lo = z) ->
    (forall (b : block) (lo hi : Z),
        In (b, lo, hi) l -> exists delta : Z, f0 b = Some (sp, delta)) ->
    MemClosures_local.unmapped_closed mu m' x.
Proof.
  clear.
  induction l;intros until z;intros ? ? AGMU SVALID TVALID NGE S_EQ RCPRESV R R2.
  {
    clear R R2.
    inv H.
    unfold Mem.free_list in H0.
    simpl in *. 
    inv RCPRESV.
    
    econstructor;eauto.
    {
      intros.
      
      eapply Mem.perm_free_3 in H2;eauto.
      assert(b' <> sp).
      intro;subst. inv AGMU.
      inv proper_mu_ge_init_inj.
      rewrite mu_shared_tgt in H;unfold Bset.belongsto in H.
      rewrite<- S_EQ in H. contradiction.
      Transparent Mem.free.
      unfold Mem.free in *.
      unfold Mem.unchecked_free in *.
      inv_eq.
      Opaque Mem.free.
      eauto.
    }
    {
      intros.
      eapply Mem.perm_free_3 in H2;eauto.
      assert(b' <> sp).
      intro;subst. inv AGMU.
      inv proper_mu_ge_init_inj.
      rewrite mu_shared_tgt in H;unfold Bset.belongsto in H.
      rewrite<- S_EQ in H. contradiction.
      Transparent Mem.free.
      unfold Mem.free in *.
      unfold Mem.unchecked_free in *.
      inv_eq.
      Opaque Mem.free.
      eauto.
    }
    {
      intros.
      eapply Mem.perm_free_3 in H2;eauto.
      assert(b' <> sp).
      intro;subst. inv AGMU.
      inv proper_mu_ge_init_inj.
      rewrite mu_shared_tgt in H;unfold Bset.belongsto in H.
      rewrite<- S_EQ in H. contradiction.
      Transparent Mem.free.
      unfold Mem.free in *.
      unfold Mem.unchecked_free in *.
      inv_eq.
      Opaque Mem.free.
      eauto.
    }
  }
  {
    simpl in H.
    inv_eq.
    exploit IHl;eauto.
    intros.
    eapply Mem.valid_block_free_1;eauto.
    exploit R2;eauto. intros [].

    exploit R;eauto. intros[].
    subst.
    
    inv RCPRESV.
    econstructor;intros.
    {
      eapply unmapped_closure;eauto.
      intros.
      apply H4 in H7 as ?.
      intro. contradict H8.
      assert(b1<>b).
      intro;subst. inv AGMU. apply proper_mu_inject in H7.
      inv proper_mu_ge_init_inj.
      rewrite mu_shared_src in H7;unfold Bset.belongsto in H7.
      rewrite S_EQ in H7.
      contradiction.

      eapply Mem.perm_free_1 in Heqo;eauto.
    }
    {
      eapply unmapped_no_undef;eauto.
      intros.
      apply H4 in H6 as ?.
      intro. contradict H7.
      assert(b0<>b).
      intro;subst. inv AGMU. apply proper_mu_inject in H6.
      inv proper_mu_ge_init_inj.
      rewrite mu_shared_src in H6;unfold Bset.belongsto in H6.
      rewrite S_EQ in H6.
      contradiction.

      eapply Mem.perm_free_1 in Heqo;eauto.
    }
    {
      eapply unmapped_no_vundef;eauto.
      intros.
      apply H4 in H6 as ?.
      intro. contradict H7.
      assert(b0<>b).
      intro;subst. inv AGMU. apply proper_mu_inject in H6.
      inv proper_mu_ge_init_inj.
      rewrite mu_shared_src in H6;unfold Bset.belongsto in H6.
      rewrite S_EQ in H6.
      contradiction.

      eapply Mem.perm_free_1 in Heqo;eauto.
    }
  }
Qed.