From mathcomp.ssreflect Require Import fintype ssrnat.  
Require Import Coqlib Maps Axioms Values Integers.
Require Import Blockset CUAST AST Globalenvs.
Require Import LDSim LDSimDefs Injections InjRels ValRels.
Require Import InteractionSemantics SpecLang SpecLangWDDET.
Require Import MemClosures Memdata Memperm MemAux FMemLemmas GMemory FMemory Footprint TSOMemLemmas.

Lemma LfpG_loadb:
  forall (sge tge:genv)mu fl b b' id
    (SFIND:Genv.find_symbol sge id = Some b)
    (TFIND:Genv.find_symbol tge id = Some b')
    (INJB:inj mu b = Some b'),
    ge_init_inj mu sge tge->
    no_overlap fl (SharedTgt mu) ->
    LfpG' fl mu (loadmax_fp b)(loadmax_fp b').
Proof.
  intros. unfold loadmax_fp,FMemOpFP.load_fp,FMemOpFP.range_locset,Locs.belongsto.
  inv H. unfold Senv.find_symbol,Genv.to_senv,F,V in senv_injected.
  specialize (senv_injected id).
  rewrite SFIND,TFIND in senv_injected. inv senv_injected.
  constructor.
  constructor;try apply FMemOpFP.emp_loc_match.
  unfold FP.ge_reads;simpl;constructor;unfold Locs.belongsto;intros.
  ex_match. subst b0.
  Esimpl. eauto.
  unfold Locs.union. apply orb_true_iff. left.
  ex_match2.

  constructor. unfold Bset.belongsto,FP.blocks,FP.locs,Locs.blocks,Locs.belongsto in H. simpl in H.
  rewrite ! Locs.emp_union_locs in H.
  rewrite Locs.locs_union_emp in H.
  Hsimpl.
  ex_match. subst b0.
  inv mu_inject.
  inv inj_weak.
  eapply inj_range';eauto.
Qed.
Lemma LfpG_storeb:
  forall (sge tge:genv) mu fl b b' id
    (SFIND:Genv.find_symbol sge id = Some b)
    (TFIND:Genv.find_symbol tge id = Some b')
    (INJB:inj mu b = Some b'),
    ge_init_inj mu sge tge->
    no_overlap fl (SharedTgt mu) ->
    LfpG' fl mu (storemax_fp b)(storemax_fp b').
Proof.
  intros. unfold storemax_fp,FMemOpFP.store_fp,FMemOpFP.range_locset,Locs.belongsto.
  inv H. unfold Senv.find_symbol,Genv.to_senv,F,V in senv_injected.
  specialize (senv_injected id).
  rewrite SFIND,TFIND in senv_injected. inv senv_injected.
  constructor.
  constructor;try apply FMemOpFP.emp_loc_match.
  unfold FP.ge_writes;simpl;constructor;unfold Locs.belongsto;intros.
  ex_match. subst b0.
  Esimpl. eauto.
  unfold Locs.union. apply orb_true_iff. left.
  ex_match2.

  constructor. unfold Bset.belongsto,FP.blocks,FP.locs,Locs.blocks,Locs.belongsto in H. simpl in H.
  rewrite ! Locs.emp_union_locs in H.
  rewrite Locs.locs_union_emp in H.
  Hsimpl.
  ex_match. subst b0.
  inv mu_inject.
  inv inj_weak.
  eapply inj_range';eauto.
Qed.
Definition reachable_closure (m:gmem)(B:Bset.t):=
  forall b,
    reachable m B b->
    Bset.belongsto B b.
Definition rc2 (m:gmem)(B:Bset.t):=
  forall b,
    Bset.belongsto B b ->
    forall ofs b' ofs' q n,
      GMem.perm m b ofs Max Readable ->
      ZMap.get ofs (GMem.mem_contents m)!!b = Fragment (Vptr b' ofs') q n->
      Bset.belongsto B b'.

Lemma rc_eq:
  forall m B,
    reachable_closure m B <-> rc2 m B.
Proof.
  unfold reachable_closure,rc2.
  split;intro.
  {
    intros.
    apply H.
    econstructor.
    econstructor 2;eauto.
    econstructor. auto.
  }
  {
    intros.
    inv H0.
    generalize dependent b.
    induction L;intros.
    inv H1;auto.
    inv H1.

    apply IHL in H3 as ?.
    exploit H;eauto.
  }
Qed.
Definition no_undef (m:gmem)(B:Bset.t):Prop:=
  forall b,
    B b ->
    forall ofs,
    GMem.perm m b ofs Max Readable->
    ZMap.get ofs (GMem.mem_contents m)!!b <> Undef.
Definition no_frag_undef (m:gmem)(B:Bset.t):Prop:=
  forall b,
    B b->
    forall ofs,
      GMem.perm m b ofs Max Readable->
      forall q n,
        ZMap.get ofs (GMem.mem_contents m)!! b <> Fragment Vundef q n.

Record nundef (m:gmem)(B:Bset.t):Prop:=
  {
    no_undef': no_undef m B;
    no_frag_undef': no_frag_undef m B
  }.


Local Notation "a # b" := (PMap.get b a) (at level 1).


Lemma LfpG_emp:
  forall mu fl fp, LfpG' mu fl fp FP.emp.
  constructor;constructor;try constructor;intros;try inv H;try inv H0.
Qed.
Lemma embed_preserve:
  forall fl m fm,
    embed m fl fm->
    forall m',
      GMem.forward m m'->
      unchg_freelist fl m m'->
      exists fm', embed m' fl fm'.
Proof.
  intros.
  inv H.
  inv H1.
  pose proof gmem_fl_wd_embed.
  pose proof fmem_strip_fl_wd fm.
  assert(gmem_fl_wd m' (Mem.freelist fm)(Mem.nextblockid fm)).
  inv H1.
  constructor;auto.
  intros.
  apply valid_wd0 in H1 as ?.
  unfold get_block in H1. unfold in_fl in unchanged_on_validity.
  assert(exists n, Streams.Str_nth n (Mem.freelist fm) = b).
  eauto.
  specialize (unchanged_on_validity _ 0 H3) as ?.
  clear H1 H3.
  unfold GMem.valid_block in H4.
  split;intro;eauto. apply H4 in H1. apply H2. auto.
  apply H2 in H1. apply H4. auto.

  eexists. eapply H with(wd:=H2);eauto.
Qed.
Lemma fmem_valid_wd:
  forall (m:mem) n b,
    get_block m.(Mem.freelist) n = b ->
    In b m.(Mem.validblocks) <-> (n<m.(Mem.nextblockid))%coq_nat.
Proof.  destruct m;simpl;intros;auto. Qed.
Lemma init_embed:
  forall (sge tge:genv) mu sfl tfl sm tm,
    ge_init_inj mu sge tge->
    init_gmem tge tm->
    local_init_rel mu sfl sm tfl tm->
    exists fm, embed tm tfl fm.
Proof.
  unfold init_gmem; intros.
  Hsimpl.
  inv H2.
  unfold Mem.valid_block in dom_match_fm.
  pose proof fmem_valid_wd x as x_valid_wd.
  enough(gmem_fl_wd (strip x) tfl 0).
  Hsimpl.
  eexists; eapply gmem_fl_wd_embed with(wd:=H0) ;eauto.

  inv H1.
  unfold valid_block_bset,GMem.valid_block,strip in tfl_free;simpl in tfl_free.
  econstructor;eauto.
  inv tfl_norep;auto.
  unfold strip;simpl.
  intros.
  
  apply tfl_free in H0.
  unfold Bset.belongsto in H0.
  split;intro;try contradiction;try omega.
Qed.



Local Ltac solv_eq:=
  match goal with
  | [H1: ?P , H2 : ?P |- _] => clear H1
  | [H1: ?P = _, H2: ?P = _ |- _] =>
    rewrite H1 in H2; inv H2
  | [H1: ?P = _ , H2: _ = ?P |- _] =>
    rewrite H1 in H2; inv H2
  | [H1: _ = ?P, H2: _ = ?P |- _] =>
    rewrite <- H1 in H2; inv H2
  end.
Record ge_lessmatch {F1 V1 : Type} (sge : Genv.t F1 V1) 
(tge : Genv.t F1 V1) : Prop := Build_ge_match
  { genv_public_eq : forall id : ident,
                     In id (Genv.genv_public sge) <-> In id (Genv.genv_public tge);
    genv_symb_eq_dom : forall id : positive,
                       (Genv.genv_symb sge) ! id = None <->
                       (Genv.genv_symb tge) ! id = None;
    genv_defs_match : forall (id : positive) (b b' : block),
                      (Genv.genv_symb sge) ! id = Some b ->
                      (Genv.genv_symb tge) ! id = Some b' ->
                      option_rel globdef_match (Genv.genv_defs sge) ! b
                        (Genv.genv_defs tge) ! b';}.

Lemma ge_related_ge_lessmatch{F V}:forall ge ge', @ge_related F V ge ge'->@ge_lessmatch F V ge ge'.
Proof.
  inversion 1;subst.
  constructor. split;congruence.
  intro;specialize (H3 id).
  inv H3;split;intro;try congruence;unfold Genv.find_symbol in *;try solv_eq;try congruence.
  intros.
  specialize (H3 id). inv H3;unfold Genv.find_symbol in *;solv_eq;try congruence.
  solv_eq.
  erewrite H6;eauto.
  destruct (Genv.genv_defs ge)!b eqn:?;constructor.
  destruct g;constructor.
  destruct v;constructor.
Qed.

Lemma ge_lessmatch_comm{F V}: forall x y, @ge_lessmatch F V x y -> ge_lessmatch y x.
Proof.
  destruct 1;constructor.
  split;intro;eapply genv_public_eq0;eauto.
  split;intro;eapply genv_symb_eq_dom0;eauto.
  intros. exploit genv_defs_match0;eauto.
  intro. inv H1;constructor. inv H4;constructor. inv H1;constructor.
Qed.

Lemma ge_lessmatch_trans{F V}: forall x y z,@ge_lessmatch F V x y-> ge_lessmatch y z->ge_lessmatch x z.
Proof.
  destruct 1,1.
  constructor.
  split;intro;try apply genv_public_eq0;try apply genv_public_eq1;try apply genv_public_eq0;auto.
  split;intro;try apply genv_symb_eq_dom0;try apply genv_symb_eq_dom1;try apply genv_symb_eq_dom0;auto.
  intros.
  destruct (Genv.genv_symb y)!id eqn:?.
  exploit genv_defs_match0;eauto;intro.
  exploit genv_defs_match1;eauto;intro.
  inv H1;inv H2;try congruence;try constructor;try solv_eq.
  inv H7;inv H5;try congruence;try constructor;try solv_eq.
  inv H1;inv H8;try congruence;try constructor.
  eapply genv_symb_eq_dom0 in Heqo;eauto. congruence.
Qed.
Section MEMORY.
Record mem_rel (j:Bset.inj)(m1 m2:gmem):Prop:=
  {
    injective: forall b b' b'', j b = Some b'-> j b'' = Some b' -> b = b'';
    valid_block_rel: forall b b', j b = Some b' -> GMem.valid_block m1 b /\ GMem.valid_block m2 b';
    perm_rel: forall b b', j b = Some b' ->forall ofs k p,GMem.perm m1 b ofs k p -> GMem.perm m2 b' ofs k p;
    perm_rel2: forall b b', j b = Some b' ->forall ofs k p,GMem.perm m2 b' ofs k p -> GMem.perm m1 b ofs k p \/ ~ GMem.perm m1 b ofs Max Nonempty;
    val_rel: forall b b', j b = Some b'->forall ofs,GMem.perm m1 b ofs Max Readable -> memval_related j (ZMap.get ofs (GMem.mem_contents m1)!!b)(ZMap.get ofs (GMem.mem_contents m2)!!b')
  }.
(*  
Definition memval_rel (f:Bset.inj)(m1 m2:gmem):Prop:=
  forall b1 ofs1 b2,
    f b1 = Some b2 ->
    GMem.perm m1 b1 ofs1 Max Readable->
    memval_related f (ZMap.get ofs1 (GMem.mem_contents m1)!!b1)
                   (ZMap.get ofs1 (GMem.mem_contents m2)!!b2).

Definition mem_rel (j:Bset.inj)(m1 m2:gmem):Prop:=
  GMem.inject (Bset.inj_to_meminj j) m1 m2 /\
  memval_rel j m1 m2 /\
  Bset.inj_inject j.
 *)
Lemma mem_rel_range_perm_eq:
  forall j m1 m2 b lo hi k p b',
    mem_rel j m1 m2->
    j b = Some b'->
    GMem.range_perm m1 b lo hi k p-> GMem.range_perm m2 b' lo hi k p.
Proof. unfold GMem.range_perm;intros;  eapply H1 in H2;eapply H;eauto. Qed.
Lemma loadmax_memrel:
  forall j m1 m2 b1 b2 v1,
    mem_rel j (strip m1) (strip m2) ->
    loadmax m1 b1 = Some v1 ->
    j b1 = Some b2 ->
    exists v2, loadmax m2 b2 = Some v2 /\ val_related j v1 v2.
Proof.
  intros. 
  unfold loadmax in *. ex_match.
  assert(Mem.range_perm m2 b2 0 4 Max Readable).
  eapply mem_rel_range_perm_eq in H;eauto.
  
  eexists;split;eauto.
  ex_match2;eauto. contradiction.
  inv H0.
  eapply decode_val_related;eauto.
  unfold Bset.inj_inject. intros.
  eapply H in H0;try apply H3;eauto.
  repeat (econstructor;[eapply H;eauto;eapply r;eauto;  simpl; omega|]).
  constructor.
Qed.
Lemma storemax_permeq:
  forall m b v m' b' z p k,
    storemax m b v = Some m'->
    Mem.perm m b' z p k <->
    Mem.perm m' b' z p k.
Proof.
  unfold storemax;intros.
  ex_match. inv H.
  unfold Mem.perm;simpl;split;auto.
Qed.
Lemma storemax_memrel:
  forall j m1 m2 b1 b2 v1 v2 m1',
    mem_rel j (strip m1)(strip m2) ->
    storemax m1 b1 v1 = Some m1'->
    val_related j v1 v2->
    j b1 = Some b2 ->
    exists m2',storemax m2 b2 v2 = Some m2' /\ mem_rel j (strip m1')(strip m2').
Proof.
  intros.
  unfold storemax in *.
  ex_match.

  assert(Mem.range_perm m2 b2 0 (size_chunk Mint32) Max Writable).
  eapply mem_rel_range_perm_eq in H;eauto.

  eexists. ex_match2. split;eauto.
  inv H0.
  unfold strip;simpl.
  
  constructor;auto;try apply H.
  unfold GMem.perm;simpl.
  intros.
  eapply val_rel in H0 as ?;eauto.
  do 2 rewrite PMap.gsspec.
  destruct peq.
  {
    subst. rewrite H2 in H0;inv H0.
    ex_match2.
    eapply memval_related_memval_inject_strict.
    eapply setN_memval_related;eauto.
    unfold Bset.inj_inject.
    intros.
    eapply injective;eauto.
    eapply memval_related_memval_inject_strict;eauto.
  }
  {
    assert(b' <> b2).
    intro. contradict n. subst.
    eapply H;eauto.
    ex_match2;auto.
  }
Qed.


Lemma alloc_memrel:
  forall j m1 m2 lo hi m1' b1,
    mem_rel j (strip m1)(strip m2) ->
    Mem.alloc m1 lo hi = (m1',b1) ->
    exists j' m2' b2,
      Mem.alloc m2 lo hi = (m2',b2) /\
      mem_rel j' (strip m1')(strip m2') /\
      (forall b b', j b = Some b' -> j' b = Some b') /\
      (forall b, b<> b1 -> forall b', j' b = Some b'->j b = Some b') /\
      j' b1 = Some b2.
Proof.
  Transparent Mem.alloc.
  intros.
  assert(R0:forall m,~Mem.valid_block m (Mem.nextblock m)).
  intros []. unfold Mem.valid_block,Mem.nextblock;simpl;intro.
  exploit valid_wd;eauto.
  intro. apply H2 in H1. apply Nat.lt_neq in H1. contradiction.
  assert(R: j b1 = None).
  apply Mem.alloc_result in H0.
  specialize (R0 m1). subst.
  destruct (j (Mem.nextblock m1)) eqn:?;auto.
  apply H in Heqo as []. contradict R0. auto.
  assert(R2:forall b, j b <> Some (Mem.nextblock m2)).
  intros. intro. apply H in H1 as [].
  specialize (R0 m2).
  contradict R0. auto.
  exists (fun b =>if peq b b1 then Some (Mem.nextblock m2) else j b).
  unfold Mem.alloc in *.  inv H0.
  unfold strip;simpl.
  Esimpl;eauto;simpl.
  {
    constructor;try apply H.
    {
      intros. ex_match2. eapply H;eauto.
    }
    {
      unfold GMem.valid_block;simpl.
      intros.
      ex_match2;try eapply H;eauto.
      inv H0. split;auto.
      eapply valid_block_rel in H0;eauto.
      unfold GMem.valid_block,strip in H0. simpl in H0.
      destruct H0.
      split;auto.
    }
    {
      unfold GMem.perm;simpl.
      intros. ex_match2;subst.
      + inv H0. rewrite! PMap.gss in *. auto.
      + specialize (R2 b). rewrite H0 in R2.
        assert(b' <> Mem.nextblock m2). intro;subst;contradict R2;auto.
        rewrite ! PMap.gso in *;auto.
        eapply H;eauto.
    }
    {
      unfold GMem.perm;simpl.
      intros. ex_match2;subst.
      + inv H0. rewrite! PMap.gss in *. auto.
      + specialize (R2 b). rewrite H0 in R2.
        assert(b' <> Mem.nextblock m2). intro;subst;contradict R2;auto.
        rewrite ! PMap.gso in *;auto.
        eapply H;eauto.
    }
    {
      simpl. unfold GMem.perm;simpl.
      intros;ex_match2.
      + inv H0. rewrite ! PMap.gss,! ZMap.gi. constructor.
      + specialize (R2 b). rewrite H0 in R2.
        assert(b' <> Mem.nextblock m2). intro;subst;contradict R2;auto.
        rewrite ! PMap.gso;auto.
        rewrite ! PMap.gso in H1;auto.
        eapply val_rel in H;eauto.
        unfold ZMap.t,PMap.t in H.
        inv H;try constructor.
        inv H5;try constructor.
        ex_match2.
    }
  }
  all: intros;ex_match2;auto.
  Opaque Mem.alloc.
Qed.
End MEMORY.
Record unmapped_closed (mu:Mu)(m m':gmem):Prop:=
  {
    unmapped_closure: forall b ofs b' ofs' q n,
      SharedTgt mu b ->
      (forall b0, inj mu b0 = Some b -> ~ GMem.perm m b0 ofs Max Readable) ->
      GMem.perm m' b ofs Max Readable ->
      ZMap.get ofs (GMem.mem_contents m') # b = Fragment (Vptr b' ofs') q n->
      SharedTgt mu b';
    unmapped_no_undef:
      forall b ofs,
        SharedTgt mu b ->
        (forall b0, inj mu b0 = Some b -> ~ GMem.perm m b0 ofs Max Readable) ->
        GMem.perm m' b ofs Max Readable ->
        ZMap.get ofs (GMem.mem_contents m') # b <> Undef;
    unmapped_no_vundef:
      forall b ofs,
        SharedTgt mu b ->
        (forall b0, inj mu b0 = Some b -> ~ GMem.perm m b0 ofs Max Readable) ->
        GMem.perm m' b ofs Max Readable ->
        forall q n,
          ZMap.get ofs (GMem.mem_contents m') # b <> Fragment Vundef q n;
  }.
Lemma reach_closed_unmapped_closed:
  forall mu m m',
    reach_closed m' (SharedTgt mu)->
    unmapped_closed mu m m'.
Proof.
  inversion 1;subst. constructor;auto.
  apply rc_eq in reachable_closure0. unfold rc2 in reachable_closure0.
  intros.
  eapply reachable_closure0;eauto.
Qed.
Lemma mem_rel_unmapped_closed_reach_closed:
  forall mu f m m',
    Bset.inject (inj mu)(SharedSrc mu)(SharedTgt mu)->
    mem_rel f m m'->
    (forall b b', inj mu b = Some b' -> f b = Some b') ->
    unmapped_closed mu m m'->
    reach_closed m (SharedSrc mu)->
    reach_closed m' (SharedTgt mu).
Proof.
  intros.
  constructor.
  {
    intros.
    inv H4. revert L b H5. induction L;intros.
    inv H5;auto.

    inv H5. apply IHL in H7. clear IHL.
    exploit Bset.inj_range;eauto. inv H;eauto.
    intros (b'0 & INJ).
    destruct (GMem.perm_dec m b'0 z Max Readable).
    exploit val_rel;eauto.
    intro. rewrite H10 in H4. inv H4.
    inv H9.
    inv H3. apply rc_eq in reachable_closure0.
    unfold rc2 in reachable_closure0.
    symmetry in H5.
    eapply H in INJ as ?.
    eapply reachable_closure0 in H5;eauto.
    eapply H in H5;eauto. Hsimpl.
    eapply H1 in H4 as ?.
    rewrite H5 in H11. inv H11.
    eapply H;eauto.

    assert(forall b, inj mu b = Some b' -> ~ GMem.perm m b z Max Readable).
    intros. apply H1 in INJ. apply H1 in H4.
    assert(b0 = b'0).
    eapply H0;eauto. subst;auto.

    eapply H2 in H4;eauto.
  }
  {
    intros. inv H.
    eapply inj_weak in H4 as ?;eauto.
    Hsimpl.
    apply H1 in H as ?.
    destruct(GMem.perm_dec m x z Max Readable).
    intro.
    pose proof val_rel _ _ _ H0 _ _ H6 z p.
    rewrite H7 in H8. inv H8.
    symmetry in H10. contradict H10.
    eapply H3;eauto. eapply inj_weak;eauto.

    eapply H2;eauto.
    intros. eapply H1 in H;eapply H1 in H7.
    eapply H0 in H;eauto. subst. auto.
  }
  {
    intros. inv H.
    eapply inj_weak in H4 as ?;eauto.
    Hsimpl.
    apply H1 in H as ?.
    destruct(GMem.perm_dec m x z Max Readable).
    intro.
    pose proof val_rel _ _ _ H0 _ _ H6 z p.
    rewrite H7 in H8. inv H8. inv H11.
    symmetry in H9. contradict H9.
    eapply H3;eauto. eapply inj_weak;eauto.

    eapply H2;eauto.
    intros. eapply H1 in H;eapply H1 in H7.
    eapply H0 in H;eauto. subst. auto.
  }
Qed.
Lemma storemax_contents:
  forall m b v m',
    storemax m b v = Some m'->
    GMem.mem_contents (strip m') =
    PMap.set b
             (Mem.setN (encode_val Mint32 v) 0
                       (Mem.mem_contents m) # b) 
             (Mem.mem_contents m).
Proof.
  unfold storemax;intros.
  ex_match.
  inv H. auto.
Qed.
Lemma storemax_unmapped_closed_preserve:
  forall mu f m1 b1 v1 m2 b2 v2 m1' m2',
    Bset.inject (inj mu)(SharedSrc mu)(SharedTgt mu) ->
    mem_rel f (strip m1)(strip m2) ->
    (forall b b', inj mu b = Some b' -> f b = Some b') ->
    unmapped_closed mu (strip m1)(strip m2) ->
    storemax m1 b1 v1 = Some m1' ->
    storemax m2 b2 v2 = Some m2' ->
    f b1 = Some b2 ->
    unmapped_closed mu (strip m1')(strip m2').
Proof.
  intros.
  constructor.
  {
    intros. erewrite storemax_contents in H9;eauto.
    eapply storemax_permeq in H4 as ?;eauto.
    eapply H10 in H8;eauto.
    clear H10.
    rewrite PMap.gsspec in H9.
    destruct peq.
    {
      subst.
      destruct (zlt ofs 0). rewrite Mem.setN_outside in H9; auto.
      eapply unmapped_closure;eauto. intros.
      intro. eapply H7;eauto. eapply storemax_permeq in H3;eauto.
      eapply H3;eauto.

      destruct (zlt ofs 4).  Focus 2. rewrite Mem.setN_outside in H9;eauto.
      Focus 2. simpl. erewrite minlength. eauto.
      eapply unmapped_closure;eauto. intros.
      intro. eapply H7;eauto. eapply storemax_permeq in H3;eauto.
      eapply H3;eauto.

      exploit Bset.inj_range;eauto.
      inv H;eauto. intros [].
      apply H1 in H10 as ?.
      eapply H0 in H5;eauto. subst.
      eapply H7 in H10. contradict H10.
      pose proof H3 as R.
      unfold storemax in R.
      ex_match. clear R.
      apply Mem_writable_imp_readable in r as ?.
      exploit H5. split;eauto. omega.
      intro. eapply storemax_permeq in H3;eauto.
      eapply H3;eauto.
    }
    {
      eapply H2;eauto.
      intros. intro.
      eapply H7;eauto.
      eapply storemax_permeq in H3;eauto.
      eapply H3;eauto.
    }
  }
  {
    intros. erewrite storemax_contents;eauto.
    eapply storemax_permeq in H4 as ?;eauto.
    eapply H9 in H8;eauto.
    clear H9.
    rewrite PMap.gsspec.
    destruct peq.
    {
      subst.
      destruct (zlt ofs 0). rewrite Mem.setN_outside; auto.
      eapply H2;eauto. intros.
      intro. eapply H7;eauto. eapply storemax_permeq in H3;eauto.
      eapply H3;eauto.

      destruct (zlt ofs 4).  Focus 2. rewrite Mem.setN_outside;eauto.
      Focus 2. simpl. erewrite minlength. eauto.
      eapply H2;auto. intros.
      intro. eapply H7;eauto. eapply storemax_permeq in H3;eauto.
      eapply H3;eauto.

      exploit Bset.inj_range;eauto.
      inv H;eauto. intros [].
      apply H1 in H9 as ?.
      eapply H0 in H5;eauto. subst.
      eapply H7 in H9. contradict H9.
      pose proof H3 as R.
      unfold storemax in R.
      ex_match. clear R.
      apply Mem_writable_imp_readable in r as ?.
      exploit H5. split;eauto. omega.
      intro. eapply storemax_permeq in H3;eauto.
      eapply H3;eauto.
    }
    {
      eapply H2;eauto.
      intros. intro.
      eapply H7;eauto.
      eapply storemax_permeq in H3;eauto.
      eapply H3;eauto.
    }
  }
  {
    intros. erewrite storemax_contents;eauto.
    eapply storemax_permeq in H4 as ?;eauto.
    eapply H9 in H8;eauto.
    clear H9.
    rewrite PMap.gsspec.
    destruct peq.
    {
      subst.
      destruct (zlt ofs 0). rewrite Mem.setN_outside; auto.
      eapply H2;eauto. intros.
      intro. eapply H7;eauto. eapply storemax_permeq in H3;eauto.
      eapply H3;eauto.

      destruct (zlt ofs 4).  Focus 2. rewrite Mem.setN_outside;eauto.
      Focus 2. simpl. erewrite minlength. eauto.
      eapply H2;auto. intros.
      intro. eapply H7;eauto. eapply storemax_permeq in H3;eauto.
      eapply H3;eauto.

      exploit Bset.inj_range;eauto.
      inv H;eauto. intros [].
      apply H1 in H9 as ?.
      eapply H0 in H5;eauto. subst.
      eapply H7 in H9. contradict H9.
      pose proof H3 as R.
      unfold storemax in R.
      ex_match. clear R.
      apply Mem_writable_imp_readable in r as ?.
      exploit H5. split;eauto. omega.
      intro. eapply storemax_permeq in H3;eauto.
      eapply H3;eauto.
    }
    {
      eapply H2;eauto.
      intros. intro.
      eapply H7;eauto.
      eapply storemax_permeq in H3;eauto.
      eapply H3;eauto.
    }
  }
Qed.
Lemma alloc_valid_change_result:
  forall m lo hi m' b,
    Mem.alloc m lo hi = (m',b) ->
    forall b',
      Mem.valid_block m' b' ->
      ~ Mem.valid_block m b' ->
      b = b'.
Proof.
  unfold Mem.valid_block;intros.
  erewrite Mem.alloc_validblocks in H0;eauto.
  simpl in H0. destruct H0;try contradiction.
  apply Mem.alloc_result in H. congruence.
Qed.
Lemma alloc_unmapped_closed_preserve:
  forall mu f f' m1 lo hi m1' b1 m2 m2' b2,
    Bset.inject (inj mu)(SharedSrc mu)(SharedTgt mu) ->
    mem_rel f (strip m1)(strip m2) ->
    (forall b b', inj mu b = Some b' -> f b = Some b')->
    (forall b b', f b = Some b' -> f' b = Some b') ->
    unmapped_closed mu (strip m1)(strip m2) ->
    Mem.alloc m1 lo hi = (m1', b1) ->
    Mem.alloc m2 lo hi = (m2', b2) ->
    mem_rel f' (strip m1')(strip m2') ->
    f' b1 = Some b2 ->
    unmapped_closed mu (strip m1')(strip m2').
Proof.
  intros.
  constructor.
  {
    intros.
    destruct (in_dec eq_block b (GMem.validblocks (strip m2))).
    {
      erewrite<- GMem_contents_get_block_alloc_eq with(fsm:=m2) in H11;eauto.
      eapply Mem.perm_alloc_4 in H10;eauto.
      eapply H3;eauto.
      intros. apply H9 in H12.
      intro;contradict H12.
      eapply Mem.perm_alloc_1;eauto.
      intro.
      apply Mem.alloc_result in H5;subst.
      unfold GMem.validblocks,strip in i.
      pose proof next_block_not_in_validblock m2.
      contradiction.
    }
    {
      apply Memperm_validblock in H10 as ?.
      exploit alloc_valid_change_result;eauto.
      intro;subst.
      apply H in H8 as ?.
      Hsimpl.
      apply H1 in H13 as ?. apply H2 in H14.
      eapply H6 in H7;eauto;subst.
      apply H9 in H13.
      contradict H13.
      eapply Mem.perm_alloc_3 in H10;eauto.
      eapply Mem.perm_alloc_2 with(k:=Max) in H4;eauto.
      unfold GMem.perm,strip;simpl.
      unfold Mem.perm in H4.
      unfold Mem.perm_order' in H4.
      destruct ((Mem.mem_access m1')#b1 ofs Max) eqn:?;try contradiction.
      inv H4;econstructor.
    }
  }
  {
    intros.
    destruct (in_dec eq_block b (GMem.validblocks (strip m2))).
    {
      erewrite <-GMem_contents_get_block_alloc_eq;eauto.
      eapply Mem.perm_alloc_4 in H10;eauto.
      eapply H3;eauto.
      intros. apply H9 in H11.
      intro;contradict H11.
      eapply Mem.perm_alloc_1;eauto.
      intro;apply Mem.alloc_result in H5;subst.
      unfold GMem.validblocks,strip in i.
      pose proof next_block_not_in_validblock m2.
      contradiction.
    }
    {
      apply Memperm_validblock in H10 as ?.
      exploit alloc_valid_change_result;eauto.
      intro;subst.
      apply H in H8 as ?. Hsimpl.
      apply H1 in H12 as ?. apply H2 in H13.
      eapply H6 in H7;eauto;subst.
      apply H9 in H12. contradict H12.
      eapply Mem.perm_alloc_3 in H10;eauto.
      eapply Mem.perm_alloc_2 with(k:=Max) in H4;eauto.
      unfold GMem.perm,strip,Mem.perm,Mem.perm_order' in *;simpl in *.
      destruct ((Mem.mem_access m1')#b1 ofs Max) eqn:?;try contradiction.
      inv H4;econstructor.
    }
  }
  {
    intros.
    destruct (in_dec eq_block b (GMem.validblocks (strip m2))).
    {
      erewrite <-GMem_contents_get_block_alloc_eq;eauto.
      eapply Mem.perm_alloc_4 in H10;eauto.
      eapply H3;eauto.
      intros. apply H9 in H11.
      intro;contradict H11.
      eapply Mem.perm_alloc_1;eauto.
      intro;apply Mem.alloc_result in H5;subst.
      unfold GMem.validblocks,strip in i.
      pose proof next_block_not_in_validblock m2.
      contradiction.
    }
    {
      apply Memperm_validblock in H10 as ?.
      exploit alloc_valid_change_result;eauto.
      intro;subst.
      apply H in H8 as ?. Hsimpl.
      apply H1 in H12 as ?. apply H2 in H13.
      eapply H6 in H7;eauto;subst.
      apply H9 in H12. contradict H12.
      eapply Mem.perm_alloc_3 in H10;eauto.
      eapply Mem.perm_alloc_2 with(k:=Max) in H4;eauto.
      unfold GMem.perm,strip,Mem.perm,Mem.perm_order' in *;simpl in *.
      destruct ((Mem.mem_access m1')#b1 ofs Max) eqn:?;try contradiction.
      inv H4;econstructor.
    }
  }
Qed.
Definition match_tmp (f:Bset.inj)(t1 t2:tmp):Prop:=
  forall id,
    val_related f (t1 id)(t2 id).
Definition setid (te:tmp)(va:ident)(vb:val):tmp:=
  fun b => if peq b va then vb else te b.
Lemma setid_comm:
  forall t v1 v2 a1 a2,
    a1 <> v1->
    setid (setid t v1 v2) a1 a2 = setid (setid t a1 a2) v1 v2.
Proof.
  unfold setid.
  intros.
  apply functional_extensionality.
  intro. destruct peq;auto.
  subst. rewrite peq_false;auto.
Qed.
Lemma setid_set:
  forall t v1 v2 v3,
    setid (setid t v1 v2) v1 v3 = setid t v1 v3.
Proof.
  unfold setid.
  intros.
  apply functional_extensionality.
  intros. destruct peq;auto.
Qed.
Lemma setid_match_tmp:
  forall j t1 t2 id v1 v2,
    match_tmp j t1 t2->
    val_related j v1 v2->
    match_tmp j (setid t1 id v1)(setid t2 id v2).
Proof.
  unfold match_tmp,setid;intros.
  destruct peq;eauto.
Qed.
Definition match_stmt (f:Bset.inj)(s1 s2:stmt):Prop:= s1 = s2.

Inductive match_cont:Bset.inj->cont->cont->Prop:=
| match_Kstop:
    forall f,
      match_cont f Kstop Kstop
| match_Kseq:
    forall f s1 s2 t1 t2,
      match_stmt f s1 s2 ->
      match_cont f t1 t2 ->
      match_cont f (Kseq s1 t1)(Kseq s2 t2).

Lemma match_cont_eq:
  forall f t1 t2, match_cont f t1 t2 -> t1 = t2.
Proof. induction 1;congruence. Qed.

Inductive match_core :Bset.inj-> core->core->Prop:=
| match_call_state:
    forall f s,
      match_core f (CallStateIn s)(CallStateIn s)
| match_core_state:
    forall f s k te k' te',
      match_cont f k k'->
      match_tmp f te te'->
      match_core f (State s k te)(State s k' te')
| match_entatom_state:
    forall f s k te k' te',
      match_cont f k k'->
      match_tmp f te te'->
      match_core f (EntAtomState s k te)(EntAtomState s k' te')
| match_atom_state:
    forall f s k k0 te k' k0' te',
      match_cont f k k'->
      match_cont f k0 k0'->
      match_tmp f te te'->
      match_core f (AtomState s k k0 te)(AtomState s k' k0' te')
| match_ext_state:
    forall f k te k' te',
      match_cont f k k'->
      match_tmp f te te'->
      match_core f (ExtAtomState k te)(ExtAtomState k' te').
  
Definition mu_inv (mu:Mu)(sfl tfl:freelist):Prop:=
  Bset.inject (inj mu) (SharedSrc mu) (SharedTgt mu)/\
  norep sfl /\ norep tfl /\
  no_overlap sfl (SharedSrc mu) /\
  no_overlap tfl (SharedTgt mu).

Definition inj_inv (j:Bset.inj)(mu:Mu)(sfl tfl:freelist):Prop:=
  forall b b',
    j b = Some b' ->
    ( in_fl sfl b /\ in_fl tfl b') \/
    ( inj mu b = Some b').

Definition inj_j (j:Bset.inj):Prop:=
  forall b b' b'',
    j b = Some b'->
    j b'' = Some b'->
    b = b''.
Lemma rc_rc2:
  forall m b,
    reach_closed m b -> rc2 m b.
Proof. inversion 1;subst;apply rc_eq;auto. Qed.
Lemma rc_nundef:
  forall m b,
    reach_closed m b-> nundef m b.
Proof. inversion 1;subst. constructor. unfold no_undef;auto. unfold no_frag_undef;auto. Qed.
Lemma rc2_nundef_rc:
  forall m b,
    rc2 m b->
    nundef m b->
    reach_closed m b.
Proof.
  intros.
  apply rc_eq in H.
  inv H0. unfold no_undef,no_frag_undef in *.
  constructor;auto.
Qed.

Definition gmeminv f mu m1 m2 sfl tfl:=
  unmapped_closed mu m1 m2/\
  mem_rel f m1 m2 /\
  inj_inv f mu sfl tfl /\
  mu_inv mu sfl tfl /\
  (forall b b', inj mu b = Some b' -> f b = Some b')/\inj_j f.
Lemma gmeminv_mu_inject:
  forall f mu sfl tfl Hm Lm,
    gmeminv f mu Hm Lm sfl tfl ->
    reach_closed Hm (SharedSrc mu) ->
    Inv mu Hm Lm.
Proof.
  unfold gmeminv,Inv;intros.
  Hsimpl.
  unfold Bset.inj_to_meminj.
  econstructor.
  {
    econstructor;intros;ex_match;inv H6.
    rewrite Z.add_0_r. eapply H1;eauto.
    apply Z.divide_0_r.
    eapply val_rel in H1;eauto.
    rewrite Z.add_0_r.
    inv H1;constructor.
    inv H9;econstructor;eauto.
    inv H0. eapply rc_eq in reachable_closure0.
    unfold mu_inv in H3. Hsimpl.
    apply i in Hx as ?.
    eapply reachable_closure0 in H7;eauto.
    exploit H7;eauto.
    intro.
    clear H7.
    eapply i in H3 as ?.
    Hsimpl.
    apply H4 in H7 as ?.
    rewrite H9 in H1. inv H1. rewrite H7. eauto.
    rewrite Ptrofs.add_zero. auto.
  }
  {
    intros.
    ex_match2.
    apply H4 in Hx .
    apply H1 in Hx as [].
    contradiction.
  }
  {
    intros. ex_match.
    inv H6. apply H4 in Hx.
    apply H1 in Hx as [];auto.
  }
  {
    unfold GMem.meminj_no_overlap.
    intros. ex_match.
    left. inv H7;inv H8.
    intro;contradict H6. subst.
    eapply H1;eauto.
  }
  {
    intros. ex_match. inv H6.
    split;auto. omega.
    rewrite Z.add_0_r.
    apply Ptrofs.unsigned_range_2.
  }
  {
    intros.
    ex_match. inv H6.
    rewrite Z.add_0_r in H7.
    eapply H1;eauto.
  }
Qed.  
Lemma gmeminv_HLRELY:
  forall f mu sfl tfl Hm Lm Hm' Lm',
    gmeminv f mu Hm Lm sfl tfl ->
    HLRely sfl tfl mu Hm Hm' Lm Lm'->
    gmeminv f mu Hm' Lm' sfl tfl.
Proof.
  pose proof True as H.
  pose proof True as H1.
  unfold gmeminv;intros;Hsimpl.
  rename H7 into INJ'.
  inv H2. inv H8;inv H7.
  Esimpl;eauto;try apply rc_nundef;auto.
  eapply reach_closed_unmapped_closed;eauto.
  unfold unchg_freelist in *.
  unfold inj_inv in H4.
  constructor.
  apply H3.
  {
    intros.
    apply H3 in H7 as [].
    apply H2 in H14. apply H8 in H7.
    split;auto.
  }
  {
    intros.
    pose proof perm_rel _ _ _ H3 _ _ H7.
    apply H4 in H7 as ?.
    destruct H16 as [[]|].
    {
      apply Memperm_validblock in H14 as ?.
      apply H12 in H18;auto.
      apply H12 in H14;auto.
      eapply H15 in H14;eauto.
      eapply H10;eauto.
      eapply Memperm_validblock;eauto.
    }
    {
      inv H9. inv mi_inj.
      eapply mi_perm in H14;eauto.
      Focus 2. unfold Bset.inj_to_meminj. rewrite H16;eauto.
      rewrite Z.add_0_r in H14. auto.
    }
  }
  {
    intros.
    pose proof perm_rel2 _ _ _ H3 _ _ H7.
    apply H4 in H7 as ?.
    destruct H16 as [[]|].
    {
      apply Memperm_validblock in H14 as ?.
      apply H10 in H18;auto.
      apply H10 in H14;auto.
      eapply H15 in H14;eauto.
      destruct H14.
      left;eapply H12;eauto;eapply Memperm_validblock;eauto.
      right;intro;contradict H14.
      apply H3 in H7 as [].
      eapply H8;eauto.
    }
    {
      inv H9. eapply mi_perm_inv;eauto.
      unfold Bset.inj_to_meminj. rewrite H16;eauto.
      rewrite Z.add_0_r. auto.
    }
  }
  {
    intros.
    apply H4 in H7 as ?.
    destruct H15 as [[]|].
    {
      apply Memperm_validblock in H14 as ?.
      apply H12 in H17 as ?;auto.
      eapply H12 in H14 as ?;eauto.
      erewrite GMem.unchanged_on_contents;eauto.
      erewrite GMem.unchanged_on_contents with(m_after:=Lm');eauto; eapply H3;eauto.
    }
    {
      apply GMem.mi_inj in H9.
      eapply GMem.mi_memval in H9;eauto.
      Focus 2.
      unfold Bset.inj_to_meminj;rewrite H15;eauto.
      rewrite Z.add_0_r in H9.
      inv H9;try constructor.
      inv H18;try constructor.
      unfold Bset.inj_to_meminj in H9;ex_match. inv H9.
      rewrite Ptrofs.add_zero. constructor;auto.

      symmetry in H16. contradict H16.
      eapply H13;eauto. inv H5. eapply H9;eauto.
      symmetry in H17;contradict H17.
      eapply H13;eauto. inv H5. eapply H9;eauto.
    }
  }
Qed.
Inductive match_state{sge tge:genv}:freelist -> freelist -> Mu -> Bset.inj -> core*gmem -> core*gmem -> Prop:=
| mk_match_state:
    forall sc tc sm tm j sfl tfl mu
      (GEINIT:ge_init_inj mu sge tge)
      (TEMBED: exists tfm, embed tm tfl tfm)
      (INVINJ: gmeminv j mu sm tm sfl tfl)
      (COREINJ: match_core j sc tc )
      (AGMU: proper_mu sge tge (Bset.inj_to_meminj j) mu),
      match_state sfl tfl mu j (sc,sm)(tc,tm).


Inductive MS{sge tge} :freelist->freelist->Mu->FP.t->FP.t-> core*gmem->core*gmem->Prop :=
| mk_MS:
    forall j mu sfl tfl cm cm' fp fp'
      (MS0:@match_state sge tge sfl tfl mu j cm cm')
      (LFPG:LfpG' tfl mu fp fp'),
      MS sfl tfl mu fp fp' cm cm'.
Lemma fstep_fleq:
  forall ge c m fp c' m',
    fstep ge c m fp c' m'->
    Mem.freelist m = Mem.freelist m'.
Proof.
  inversion 1;subst.
  inv H0;subst;auto.
  unfold storemax in H3. ex_match2. inv H3. auto.
  inv H;auto. inv H0;auto. unfold storemax in H3;ex_match2;inv H3;auto.
  inv H;auto.
  apply mem_alloc_fleq in H0;auto.
Qed.
Lemma storemax_fleq:
  forall m b v m',
    storemax m b v = Some m'->
    Mem.freelist m = Mem.freelist m'.
Proof.
  unfold storemax;intros.
  ex_match.
  inv H. auto.
Qed.
Lemma storemax_perm_eq:
  forall m b v m',
    storemax m b v = Some m'->
    forall b' ofs k p,
      Mem.perm m b' ofs k p <->
      Mem.perm m' b' ofs k p.
Proof.
  unfold storemax ;intros.
  ex_match.
  inv H. unfold Mem.perm. simpl. split;auto.
Qed.

Section CORRECTNESS.
(*Variable cu: comp_unit.  
Definition ge:=(Genv.globalenv (mkprogram (cu_defs cu)(cu_public cu) 1%positive)).*)
Variable ge:genv.
Variable sge tge:genv.
Hypothesis SGEINIT: ge_related sge ge.
Hypothesis TGEINIT: ge_related tge ge.
Hypothesis S_EQ: sge.(Genv.genv_next) = tge.(Genv.genv_next).
Lemma ge_match: ge_match sge tge.
Proof.
  apply ge_related_ge_lessmatch in SGEINIT.
  apply ge_related_ge_lessmatch in TGEINIT.
  apply ge_lessmatch_comm in TGEINIT.
  eapply ge_lessmatch_trans in TGEINIT;eauto.
  inv TGEINIT. constructor;auto.
Qed.
Lemma find_symbol_def_preserved:
  forall id b fd,
    Genv.find_symbol sge id = Some b ->
    Genv.find_def sge b = Some fd ->
    exists b',
      Genv.find_symbol tge id = Some b' /\
      Genv.find_def tge b' = Some fd.
Proof.
  intros.
  inv SGEINIT.
  specialize (H6 _ _ H0) as [].
  specialize (H4 id).
  rewrite H in H4. inv H4.
  specialize (H2 _ _ _ H6 H12). subst. clear H6.
  specialize (H7 _ _ H12).
  unfold Genv.find_def in H0.
  rewrite H0 in H7.
  revert H9 H7 TGEINIT;clear;intros.
  inv TGEINIT.
  specialize (H2 id).
  rewrite <- H9 in H2. inv H2.
  apply H5 in H12.
  rewrite H7 in H12.
  Esimpl;eauto.
Qed.

Section NORMALSTEP.
Variable mu:Mu.
Hypothesis GEINITINJ: ge_init_inj mu sge tge.
Variable f:Bset.inj.
Variable sm tm:gmem.
Variable sfl tfl:freelist.
Variable Hm Lm:mem.
Hypothesis SEMBED: embed sm sfl Hm.
Hypothesis TEMBED: embed tm tfl Lm.
Hypothesis INV: gmeminv f mu sm tm sfl tfl.
Hypothesis AGMU: proper_mu sge tge (Bset.inj_to_meminj f) mu.

Lemma find_symbol_inj:
  forall id b,
    Genv.find_symbol sge id = Some b->
    exists b', Genv.find_symbol tge id = Some b' /\ inj mu b = Some b'.
Proof.
  intros.
  inv GEINITINJ.
  simpl in senv_injected.
  specialize (senv_injected id).
  rewrite H in senv_injected.
  inv senv_injected.
  eauto.
Qed.
Lemma storemax_inv:
  forall b v m',
    storemax Hm b v = Some m'->
    forall b' v',
      f b = Some b'->
      val_related f v v'->
      exists tm', storemax Lm b' v' = Some tm' /\
             gmeminv f mu (strip m') (strip tm') sfl tfl.
Proof.
  intros. pose proof INV as R. unfold gmeminv in R. Hsimpl.
  inv SEMBED. inv TEMBED.
  exploit storemax_memrel;eauto.
  intro. Hsimpl.
  exploit storemax_unmapped_closed_preserve;try eexact H3;eauto.
  inv H5;eauto.
  intro.
  Esimpl;eauto.
  unfold gmeminv.
  Esimpl;eauto.
Qed.
Lemma alloc_inv:
  forall lo hi m' b,
    Mem.alloc Hm lo hi = (m',b)->
    exists f' tm' b', Mem.alloc Lm lo hi = (tm',b') /\
           gmeminv f' mu (strip m') (strip tm') sfl tfl.
Proof.
  Transparent Mem.alloc.
  intros.
  pose proof INV as R.
  unfold gmeminv in R;Hsimpl.
  inv SEMBED. inv TEMBED.
  exploit alloc_memrel;eauto.
  intros;Hsimpl.
  Esimpl;eauto.
  instantiate(1:=x).
  unfold gmeminv.
  Esimpl;eauto.
  unfold mu_inv in H3;Hsimpl.
  eapply alloc_unmapped_closed_preserve in H6;try apply H;eauto.

  unfold inj_inv in *.
  intros.
  destruct (peq b0 b).
  + subst.
    rewrite H10 in H11;inv H11.
    left. apply Mem.alloc_result in H. apply Mem.alloc_result in H6.
    subst. unfold Mem.nextblock.
    unfold in_fl,get_block. split;eauto.
  + eapply H9 in H11;eauto.

  unfold inj_j.
  intros.
  eapply H7;eauto.
Qed.  
End NORMALSTEP.
End CORRECTNESS.

Lemma normalstep_sim:
  forall ge sge tge mu sfl tfl Hfp Hfp' Lfp s k te sm ts tk tte  tm m s' k' te' m'
    (S_EQ: Genv.genv_next sge = Genv.genv_next tge),
    ge_related sge ge->
    ge_related tge ge->
    @MS sge tge sfl tfl mu Hfp Lfp (State s k te,sm)(State ts tk tte,tm)->
    HfpG sfl mu Hfp'->
    embed sm sfl m->
    normalstep sge s k te m Hfp' s' k' te' m' ->
    exists Lfp' ts' tk' tte' Lm' Lm,
      embed tm tfl Lm /\
      normalstep tge ts tk tte Lm Lfp' ts' tk' tte' Lm' /\
      @MS sge tge sfl tfl mu (FP.union Hfp Hfp')(FP.union Lfp Lfp')(State s' k' te',strip m')(State ts' tk' tte',strip Lm').
Proof.
  intros.
  inv H1.
  inv MS0. destruct TEMBED as [Lm TEMBED].
  inv COREINJ.
  apply match_cont_eq in H7 as ?. subst.
  inv H4.
  + Esimpl;eauto.
    econstructor;eauto. reflexivity.
    econstructor;eauto;repeat rewrite FP.fp_union_emp;auto.
    instantiate(1:=j).
    econstructor;eauto.
    exists Lm. inv TEMBED. econstructor;eauto.
    inv H3;inv TEMBED;auto.
    constructor;auto.
    eapply setid_match_tmp;eauto.
  + exploit find_symbol_inj; eauto.
    intro. Hsimpl.
    inv H3;inv TEMBED.
    unfold gmeminv in INVINJ. Hsimpl.
    exploit loadmax_memrel;eauto.
    intro.
    Hsimpl.
    Esimpl;eauto. econstructor;eauto.
    econstructor;eauto. reflexivity.
    econstructor. econstructor;eauto.
    eexists. econstructor;eauto.
    constructor;auto. econstructor;eauto.
    apply setid_match_tmp;auto.
    eapply LfpG'_union;eauto.
    eapply  LfpG_loadb;eauto.
    unfold mu_inv in H10. Hsimpl;eauto.
  + exploit find_symbol_inj;eauto.
    intro;Hsimpl.
    pose proof INVINJ as ?.
    destruct H8 as [_[_[_[_ [? _]]]] ].
    apply H8 in H5 as ?.
    exploit storemax_inv;try eexact INVINJ;eauto.
    intros.
    Hsimpl.
    Esimpl;eauto.
    econstructor;eauto.
    econstructor;eauto.
    econstructor;eauto.
    apply storemax_fleq in H10 as ?. inv TEMBED.
    rewrite H13. exists x0;constructor;eauto.
    constructor;auto.
    eapply LfpG'_union;eauto.
    eapply LfpG_storeb;eauto.
    unfold gmeminv in INVINJ.
    unfold mu_inv in INVINJ.
    Hsimpl;auto.
  + inv H1.
    specialize (H12 r) as R. rewrite H4 in R. inv R.
    Esimpl;eauto. econstructor;eauto. econstructor;eauto.
    rewrite! FP.fp_union_emp.
    inv TEMBED. inv H3.
    repeat (econstructor;eauto).
  + Esimpl;eauto. econstructor 5;eauto.
    inv H1. constructor. intro;contradict H4.
    specialize (H12 r). rewrite H1 in H12;inv H12. auto.
    inv TEMBED. inv H3. rewrite !FP.fp_union_emp.
    repeat (econstructor;eauto).
  + inv H1.
    specialize (H12 r) as R. rewrite H4 in R. inv R.
    Esimpl;eauto. econstructor;eauto. econstructor;eauto.
    rewrite! FP.fp_union_emp.
    inv TEMBED. inv H3.
    repeat (econstructor;eauto).
  + Esimpl;eauto. econstructor;eauto.
    rewrite ! FP.fp_union_emp.
    inv TEMBED;inv H3.
    repeat (econstructor;eauto).
  + Esimpl;eauto. econstructor;eauto.
    rewrite ! FP.fp_union_emp.
    inv TEMBED;inv H3.
    repeat (econstructor;eauto).
    inv H7;auto.
Qed.
Lemma LfpG_LfpG':
  forall fl mu fp fp',
    LfpG fl mu fp fp'->
    LfpG' fl mu fp fp'.
Proof.
  inversion 1;subst.
  econstructor;eauto.
  inv H0.
  econstructor;eauto; apply locs_match_union_S;auto.
Qed.
  
Lemma atomstate_state_ms:
  forall s k k0 te s' k' k0' te' sge tge sfl tfl mu sfp tfp m m',
    @MS sge tge sfl tfl mu sfp tfp ((AtomState s k k0 te),m)((AtomState s' k' k0' te'),m')->
    @MS sge tge sfl tfl mu sfp tfp ((State s k te),m)((State s' k' te'),m').
Proof.
  intros.
  inv H. econstructor;eauto.
  inv MS0. econstructor;eauto.
  inv COREINJ. econstructor;eauto.
Qed.
Theorem speclangsim:
  forall cu,
    @ldsim speclang speclang cu cu.
Proof.
  unfold ldsim.
  intros.
  inv H.
  inv H0.
  set (ge:=(Genv.globalenv (mkprogram (cu_defs cu)(cu_public cu) 1%positive))) in *.
  exists nat , lt, (fun b i => @MS sge tge sfl tfl).
  constructor;intros.
  + apply lt_wf.
  + inv H. inv MS0. inv INVINJ. inv AGMU. Hsimpl. inv H5. Hsimpl;Esimpl;auto.
  + inv H. inv MS0. inv INVINJ. Hsimpl. inv H5. Hsimpl;split;auto.
  + eapply ge_match;eauto.
  + inv H. inv MS0. auto.
  + (*init*)
    {
      unfold InteractionSemantics.init_core,speclang,init_core,generic_init_core,Genv.find_funct_ptr,fundef_init in *;simpl in *.
      ex_match;subst.
      inv Hx0. inv H5.
      eapply find_symbol_def_preserved in Hx;eauto.
      Hsimpl.
      rewrite H5,H6.
      inv H4.
      eexists;split;eauto.
      {
        intros.
        exists O.
        econstructor.
        instantiate(1:=inj mu).
        econstructor;eauto.
        + exploit init_embed;eauto;intro.
          Hsimpl.
          inv H9. inv H12.
          eapply embed_preserve in H10;eauto.
        + eapply gmeminv_HLRELY;eauto.
          unfold gmeminv,inj_inv,mu_inv.
          inv H8. Hsimpl;Esimpl;eauto.
        - eapply reach_closed_unmapped_closed;eauto.
        - constructor.
          * inv H8.
            eauto.
          * intros.
            apply H8 in H12 as ?.
            eapply Bset.inj_range' in H12 as ?;eauto.
            apply valid_Src in H13. apply valid_Tgt in H14.
            split;auto.
          * inv Binj.
            apply GMem.mi_inj in bmiw_inject.
            intros.
            eapply GMem.mi_perm in bmiw_inject;eauto;[|unfold Bset.inj_to_meminj;rewrite H12;eauto]. rewrite Z.add_0_r in bmiw_inject. auto.
          * intros.
            inv Binj. eapply GMem.mi_perm_inv in bmiw_inject;eauto.
            unfold Bset.inj_to_meminj;rewrite H12;eauto.
            rewrite Z.add_0_r;eauto.
          * inv Binj.
            apply GMem.mi_inj in bmiw_inject.
            intros.
            eapply GMem.mi_memval in bmiw_inject;eauto;[|unfold Bset.inj_to_meminj;rewrite H12;eauto]. rewrite Z.add_0_r in bmiw_inject.
            {
              inv bmiw_inject;try constructor.
              inv H16;try constructor.
              unfold Bset.inj_to_meminj in H17. ex_match. inv H17.
              rewrite Ptrofs.add_zero. constructor;auto.
              symmetry in H14;contradict H14.
              eapply rc_shared_Src;eauto.
              eapply H8;eauto.
              symmetry in H15;contradict H15.
              eapply rc_shared_Src;eauto.
              eapply H8;eauto.
            }
        - inv H. auto.
        - inv H8. unfold inj_j. eauto.
        - econstructor;eauto.
        - econstructor;eauto.
            inv H;auto.
            unfold sep_inject;eauto.
            apply LfpG_emp.
      }
    }
  + (*step*)
    {
      unfold speclang in *;simpl in *.
      inv H0.
      inv H6.
      {
        pose proof H as ?.
        inv H6. inv MS0. inv COREINJ.
        exploit normalstep_sim;eauto.
        intro.
        Hsimpl.
        right.
        Esimpl;eauto. constructor. econstructor;eauto. econstructor;eauto.
        inv H8. auto.
      }
      {
        inv H. inv MS0. inv COREINJ.
        Hsimpl.
        right. 
        Esimpl;eauto.
        constructor. econstructor;eauto. econstructor 2;eauto.
        rewrite !FP.fp_union_emp;auto.
        rewrite !FP.fp_union_emp;auto.
        econstructor;eauto. econstructor;eauto.
        inv H. exists x;econstructor;eauto.
        inv H5;inv H;auto.
        econstructor;eauto.
      }
      {
        (* ent-atom ext-atom match-cont k0 preserve *)
        pose proof H as ?.
        inv H6. inv MS0. inv COREINJ.
        exploit normalstep_sim;eauto.
        econstructor;eauto. econstructor;eauto. econstructor;eauto.
        intro.
        Hsimpl.
        right.
        inv H8. inv MS0. inv COREINJ.
        repeat (econstructor;eauto).
        revert H13;clear;induction 1;econstructor;eauto.
      }
      {
        inv H. inv MS0. inv COREINJ. Hsimpl.
        right. inv H10.
        Esimpl;eauto. constructor. econstructor;eauto.
        econstructor 4.
        rewrite ! FP.fp_union_emp. auto.
        rewrite!FP.fp_union_emp.
        econstructor;eauto. econstructor;eauto.
        inv H. exists x;econstructor;eauto.
        inv H. inv H5. auto.
        econstructor;eauto.
      }
      {
        inv H.
        inv MS0;Hsimpl. inv COREINJ.
        inv H;inv H5.
        exploit alloc_inv;eauto.
        econstructor;eauto. econstructor;eauto.
        intro. Hsimpl.
        right.
        assert(LfpG' (Mem.freelist x) mu (FMemOpFP.alloc_fp m 0 0)(FMemOpFP.alloc_fp x 0 0)).
        apply LfpG_LfpG'. eapply FMemOpFP.alloc_LfpG.
        unfold gmeminv,mu_inv in INVINJ;Hsimpl;auto.
        Esimpl;eauto.
        constructor;auto. econstructor;eauto. econstructor;eauto.
        econstructor;eauto.
        eapply LfpG'_union;eauto.

        econstructor;eauto.
        econstructor;eauto.
        apply mem_alloc_fleq in H. rewrite H. exists x1;econstructor;eauto.
        econstructor;eauto;constructor.
        {
          inv AGMU;econstructor;eauto.
          unfold gmeminv in H5;Hsimpl.
          unfold inject_incr,Bset.inj_to_meminj;intros;ex_match.
          inv H12. apply H10 in Hx.  rewrite Hx. auto.

          unfold sep_inject,Bset.inj_to_meminj;intros.
          ex_match. inv H7. inv H8.
          unfold gmeminv in H5;Hsimpl.
          apply H10 in Hx0 as ?.
          unfold inj_j in H11.
          specialize (H11 _ _ _ Hx H12). subst.
          rewrite Hx0. auto.
        }
        eapply LfpG'_union;eauto.
      }
    }
  + (*at-ext*)
    {
      unfold speclang in *;simpl in *.
      unfold at_external in H0|-*.
      ex_match;subst.
      {
        inv H0.
        inv H. inv MS0. Hsimpl. inv COREINJ.
        Esimpl;eauto. constructor.
        inv LFPG. inv H4.
        constructor;auto. constructor;auto.
        inv H7.
        unfold gmeminv in INVINJ;Hsimpl.
        eapply mem_rel_unmapped_closed_reach_closed;eauto.
        inv GEINIT;auto.
        inv H7. eapply gmeminv_mu_inject;eauto.

        econstructor;eauto.
        econstructor;eauto.
        econstructor;eauto.
        apply LfpG_emp.
      }
      {
        inv H0.
        inv H;inv MS0;Hsimpl;inv COREINJ.
        Esimpl;eauto. constructor.
        inv LFPG. inv H4.
        econstructor;eauto.
        inv H7. econstructor;eauto.
        unfold gmeminv in INVINJ;Hsimpl.
        eapply mem_rel_unmapped_closed_reach_closed;eauto.
        inv H13;auto.
        eapply gmeminv_mu_inject;eauto. inv H7;auto.

        econstructor;eauto;try apply LfpG_emp.
        econstructor;eauto. econstructor;eauto.
      }
    }
  + (*aft-ext*)
    {
      unfold speclang in *;simpl in *.
      unfold after_external in *;simpl in *.
      ex_match.
      {
        inv H. inv MS0;Hsimpl;inv COREINJ.
        inv H4. unfold ores_rel in H5.
        destruct oresTgt;try contradiction.
        Esimpl;eauto.
        intros.
        exists O.
        econstructor;eauto. econstructor;eauto.
        inv H4. inv H7.
        eapply embed_preserve;eauto.
        eapply gmeminv_HLRELY;eauto.
        econstructor;eauto. constructor.
      }
      {
        inv H. inv MS0;Hsimpl;inv COREINJ.
        inv H4. unfold ores_rel in H5.
        destruct oresTgt;try contradiction.
        Esimpl;eauto. intros.
        exists O.
        econstructor;eauto. econstructor;eauto.
        inv H4;inv H7.
        eapply embed_preserve;eauto.
        eapply gmeminv_HLRELY;eauto.
        econstructor;eauto.
      }
    }
  + (*halt*)
    {
      unfold speclang in *;simpl in *.
      unfold halt in *.
      ex_match;subst.
      inv H0. inv H;inv MS0;Hsimpl;inv COREINJ.
      inv H10.
      Esimpl;eauto.
      constructor.
      constructor;auto.
      inv LFPG. econstructor;eauto.
      inv H4. inv H7.
      unfold gmeminv,mu_inv in INVINJ;Hsimpl.
      eapply mem_rel_unmapped_closed_reach_closed;eauto.
      inv LFPG. auto.
      eapply gmeminv_mu_inject;eauto.
      inv H4. inv H0. auto.
    }
Qed.