From mathcomp.ssreflect Require Import fintype ssrnat.
Require Import Coqlib Maps Axioms.
Require Import AST Integers Floats Values Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.

Require Import Asm.

Require Import CUAST FMemOpFP ValFP Op_fp String val_casted helpers.

Require Import Footprint GMemory FMemory.
Require Import GAST GlobDefs ETrace Blockset.
Require Import loadframe.

Require Import InteractionSemantics SpecLang.

Require Import FMemLemmas DetLemma.
Ltac inv_eq:=
  ex_match;
  repeat match goal with
         | H:?P , H1: ?P |- _ => clear H
         | H: ?a _ = ?a _ |- _ => inv H
         | H: ?a _ _ = ?a _ _ |- _ => inv H
         | H: false = true |- _ => inv H
         | H: true = false |- _ => inv H
         | H: None = Some _ |- _=> inv H
         | H: Some _ = None |- _=> inv H
         | H: Stuck = Next _ _ |- _ => inv H
         | H: Next _ _ = Stuck |- _ => inv 
         | H:?P = ?Q, H1:context [ ?P ] |- _ => rewrite H in H1
         | H:?P = ?Q |- context [ ?P ] => rewrite H 
         end;
  simpl in *;try contradiction;try discriminate;try congruence.
Lemma minlength:
  forall v,
    (Datatypes.length (encode_val Mint32 v)) = 4%nat.
Proof.
  induction v;simpl;auto.
Qed.
Lemma specLang_corestep_not_ext:
   corestep_not_at_external (InteractionSemantics.step speclang)
                            (InteractionSemantics.at_external speclang).
Proof.
  unfold corestep_not_at_external.
  intros.
  inv H.
  inv H1;auto.
Qed.
Lemma specLang_corestep_not_halted:
   corestep_not_halted (InteractionSemantics.step speclang)
                       (InteractionSemantics.halt speclang).
Proof.
  unfold corestep_not_halted.
  intros.
  inv H.
  inv H1;auto.
  inv H;auto.
Qed.

Lemma specLang_at_external_halted_excl:
  at_external_halted_excl (InteractionSemantics.at_external speclang)
                          (InteractionSemantics.halt speclang).
Proof.
  unfold at_external_halted_excl.
  destruct q;auto.
Qed.
Lemma specLang_eff:
  corestep_local_eff (InteractionSemantics.step speclang).
Proof.
  unfold corestep_local_eff.
  intros.
  inv H. inv H0. inv H1.
  {
    inv H;try apply LEffect_refl.
    unfold storemax,strip in *.
    inv_eq.
    constructor.
    constructor.
    constructor.
    constructor.
    all: gmem_unfolds ;try rewrite Locs.locs_union_emp in *;try rewrite Locs.emp_union_locs in * ;auto.
    all: try (split;auto;fail).
    unfold range_locset.
    intros. 
    rewrite Maps.PMap.gsspec.
    unfold eq_block in H.
    destruct peq,peq;try congruence.
    subst.
    apply Mem.setN_outside;simpl.
    
    destruct zle;try xomega.
    destruct zlt;inv H.
    
    pose proof minlength (te' r).
    rewrite H. simpl.
    xomega.
    
    split;intros;split;auto.
    intros. inv H;unfold GMem.perm, Memperm.perm_order' in *;simpl in *;try congruence.
    intros;contradiction.
  }
  all: try apply LEffect_refl.
  {
    inv H;try apply LEffect_refl.
    unfold storemax,strip in *.
    inv_eq.
    constructor.
    constructor.
    constructor.
    constructor.
    all: gmem_unfolds ;try rewrite Locs.locs_union_emp in *;try rewrite Locs.emp_union_locs in * ;auto.
    all: try (split;auto;fail).
    unfold range_locset.
    intros. 
    rewrite Maps.PMap.gsspec.
    unfold eq_block in H.
    destruct peq,peq;try congruence.
    subst.
    apply Mem.setN_outside;simpl.
    
    destruct zle;try xomega.
    destruct zlt;inv H.
    
    pose proof minlength (te' r).
    rewrite H. simpl.
    xomega.
    
    split;intros;split;auto.
    intros. inv H;unfold GMem.perm, Memperm.perm_order' in *;simpl in *;try congruence.
    intros;contradiction.
  }
  {
    eapply mem_alloc_eff;eauto.
  }
Qed.
Lemma embed_eq:
  forall fm m,
    embed (strip fm) (Mem.freelist fm) m ->
    m = fm.
Proof.
  destruct fm, m; intro; inv H. unfold strip in *; simpl in *.
  inv H1.
  assert (nextblockid = nextblockid0).
  { generalize valid_wd valid_wd0. clear. intros.
    destruct (Nat.lt_total nextblockid nextblockid0).
    eapply valid_wd0 in H; eauto. eapply valid_wd in H; eauto. omega.
    destruct H. auto.
    eapply valid_wd in H; eauto. eapply valid_wd0 in H; eauto. omega.
  }
  subst. f_equal; apply Axioms.proof_irr.
Qed.


Lemma normalstep_det:
  forall ge s k te m fp s' k' te' m',
    normalstep ge s k te m fp s' k' te' m'->
    forall fp' s'' k'' te'' m'',
      normalstep ge s k te m fp' s'' k'' te'' m''->
      fp = fp' /\ State s' k' te' = State s'' k'' te'' /\ m' = m''.
Proof.
  intros.
  inv H;inv H0;inv_eq;Esimpl;eauto.
  all: inv H1;inv H11;contradiction.
Qed.
Lemma specLang_det:
  lang_det speclang.
Proof.
  unfold lang_det.
  unfold step_det.
  intros.
  inv H;inv H0.
  inv H1.
  apply embed_eq in H;subst.
  
  inv H2;inv H3.
  all: try(Esimpl;eauto;fail).
  all: try (match goal with
              H:  normalstep _ _ _ _ _ _ _ _ _ _ |- _ => inv H
            end;fail).
  exploit normalstep_det;[eexact H|eexact H8|];intro;Hsimpl;subst;Esimpl;eauto.
  exploit normalstep_det;[eexact H|eexact H9|];intro;Hsimpl;subst;Esimpl;eauto.
  inv H1;eauto.
  inv_eq. auto.
Qed.
Lemma normalstep_loc:
  forall ge s k te m fp s' k' te' m',
    normalstep ge s k te m fp s' k' te' m'->
    forall m2 (MEMPRE:MemPre(strip m) m2 fp)(FLEQ:FreelistEq (strip m) m2 (Mem.freelist m)),
    exists m2',
      normalstep ge s k te (combine m2 (Mem.freelist m)(Mem.nextblockid m)(FreelistEq_mem_fl_wd m m2 FLEQ)) fp s' k' te' m2' /\
      LPost (strip m')(strip m2') fp (Mem.freelist m).
Proof.
  intros.
  inv H.
  all: try(Esimpl;eauto;econstructor;eauto;apply MemPostemp).
  {
    Esimpl;eauto.
    econstructor; eauto.
    unfold loadmax,combine in *. simpl in *.
    destruct Mem.range_perm_dec,Mem.range_perm_dec;try discriminate.
    clear r1.
    inv H1. f_equal;f_equal;f_equal;[|f_equal;[|f_equal;[|f_equal]]];auto.
    all: unfold loadmax_fp in *.
    1-4:inv MEMPRE;
      destruct ReadMemEq as[[A B]];
      unfold load_fp in *;simpl in *;
        erewrite H;eauto;
          try (unfold belongsto,Locs.belongsto,range_locset;ex_match2;try destruct zle,zlt;try omega;auto);
          try (unfold Mem.range_perm,Mem.perm in r0;unfold GMem.perm,strip;simpl;apply r0;omega).

    contradict n.
    unfold Mem.range_perm,Mem.perm in *;simpl.
    destruct MEMPRE as [[[_ ?] _] _ _].
    intros. eapply H;eauto.
    unfold load_fp in *;simpl in *.
    unfold belongsto,Locs.belongsto,range_locset;ex_match2;try destruct zle,zlt;try omega;auto.
    unfold Mem.range_perm,Mem.perm in r0;unfold GMem.perm,strip;simpl;apply r0;omega.


    constructor;auto.
    rewrite strip_combine.
    apply MemPost_effect_emp.
    unfold load_fp,effects;simpl.
    rewrite Locs.emp_union_locs.
    apply Locs.eq_refl.
  }
  {
    Esimpl;eauto.
    econstructor;eauto.
    unfold storemax in *.
    ex_match.
    ex_match2;eauto.
    clear H2 Hx0.
    contradict n.
    unfold Mem.range_perm in *.
    
    destruct MEMPRE as [_ _ ?].
    unfold storemax_fp,store_fp,effects,belongsto,Locs.belongsto  in EffectPermEqPre;
      simpl in *.
    rewrite Locs.locs_union_emp in *.
    intros.
    clear Hx.
    specialize (r0 ofs H).
    assert(range_locset b 0 4 b ofs = true).
    unfold range_locset.
    ex_match2.
    destruct zle,zlt;try xomega;auto.
    specialize (EffectPermEqPre _ _ H1).
    assert(GMem.perm (strip m) b ofs Memperm.Max Memperm.Writable).
    unfold GMem.perm,strip;simpl;auto.
    apply EffectPermEqPre in H2.
    unfold Mem.perm,combine. auto.

    unfold strip;simpl.
    {
      assert(Mem.freelist m = Mem.freelist m').
      unfold storemax in H2;inv_eq.
      constructor.
      Focus 2.
      unfold FreelistEq,GMem.valid_block in *;simpl;auto.
      unfold strip in FLEQ;simpl in FLEQ.
      unfold storemax in H2;ex_match.
      inv H2. simpl. auto.

      {
        unfold storemax in H2;ex_match.
        inv H2.
        destruct MEMPRE as [? ? ?].
        constructor. constructor.
        all: gmem_unfolds;auto.
        all: rewrite Locs.locs_union_emp in *.
        clear ReadMemEq.
        clear CmpMemPermExists.
        unfold belongsto,Locs.belongsto in *;split;intros; specialize (EffectPermEqPre b0 ofs H1);
          unfold Mem.range_perm in r0;unfold range_locset in H1;ex_match;
            subst;
            destruct zle,zlt;try discriminate;
              exploit r0;eauto;intro.
        apply EffectPermEqPre in H3.
        eapply Memperm_validblock;eauto.

        apply EffectPermEqPre in H3.
        eapply Mem.perm_valid_block;eauto.

        clear ReadMemEq CmpMemPermExists.
        intros.

        do 2 rewrite PMap.gsspec.
        destruct peq.
        subst.
        unfold belongsto,Locs.belongsto,range_locset in H1.
        ex_match. destruct zle,zlt;try discriminate;try xomega.
        eapply setN_geteq2;eauto.
        rewrite minlength. auto.

        unfold belongsto,Locs.belongsto,range_locset in H1.
        inv_eq.
      }
    }
  }
Qed.    
Lemma specLang_loc:
  corestep_locality_1 (InteractionSemantics.step speclang).
Proof.
  unfold corestep_locality_1.
  intros.
  inv H.
  pose proof H0 as PRE.
  inv H0.
  inv H1.
  set(m2:= combine m0 (Mem.freelist m1)(Mem.nextblockid m1)(FreelistEq_mem_fl_wd m1 m0 H3)).

  inv H2.
  eapply normalstep_loc with(FLEQ:=H3) in H0;eauto.
  Hsimpl. Esimpl;eauto. econstructor;eauto.
  instantiate(1:=  (combine m0 (Mem.freelist m1) (Mem.nextblockid m1)
                            (FreelistEq_mem_fl_wd m1 m0 H3))).
  apply gmem_fl_wd_embed.
  econstructor;eauto.
  
  Esimpl;eauto. econstructor;eauto.
  instantiate(1:=m2).
  eapply gmem_fl_wd_embed;eauto.
  econstructor;eauto.
  split;auto. apply MemPostemp.

  eapply normalstep_loc with(FLEQ:=H3) in H0;eauto.
  Hsimpl. Esimpl;eauto. econstructor;eauto.
  instantiate(1:=  (combine m0 (Mem.freelist m1) (Mem.nextblockid m1)
                            (FreelistEq_mem_fl_wd m1 m0 H3))).
  apply gmem_fl_wd_embed.
  econstructor;eauto.

  Esimpl;eauto. econstructor;eauto.
  instantiate(1:=m2).
  apply gmem_fl_wd_embed;eauto.
  econstructor;eauto. split;auto. apply MemPostemp.

  exploit MemPre_mem_alloc_LPost;eauto.
  instantiate(1:= H3).
  intros.
  Hsimpl.
  Esimpl;eauto.
  
  econstructor;eauto.
  Focus 2.
  econstructor;eauto.
  econstructor;eauto.
  rewrite strip_combine;auto.
Qed.

Lemma specLang_meminjc:
  step_mem_injc speclang.
Proof.
  unfold step_mem_injc.
  intros. inv H. eauto.
Qed.
Lemma specLang_initmem:
  init_gmem_valid' (InteractionSemantics.init_gmem speclang).
Proof.
   unfold init_gmem_valid'.
   intros. unfold InteractionSemantics.init_gmem in H. simpl in H.
   inv H. inv H1. inv H2. eapply dom_match_fm;eauto.
Qed.

Theorem SpecLang_wd: wd speclang.
Proof.
  pose specLang_corestep_not_ext.
  pose specLang_corestep_not_halted.
  pose specLang_at_external_halted_excl.
  pose specLang_eff.
  pose specLang_loc.
  pose specLang_det.
  pose specLang_meminjc.
  pose specLang_initmem.
  constructor;auto.
  {
    unfold corestep_forward.
    intros.
    inv H.
    inv H1.
    inv H;inv H0;try apply GMem.forward_refl.
    unfold storemax in H3.
    ex_match.
    inv H3. unfold strip. simpl.
    econstructor;eauto.

    inv H0;apply GMem.forward_refl.
    inv H;inv H0;try apply GMem.forward_refl.
    unfold storemax in H3.
    destruct Mem.range_perm_dec ;try discriminate.
    inv H3. unfold strip. simpl.
    econstructor;eauto.

    inv H0;apply GMem.forward_refl.
    eapply alloc_forward;eauto.
  }
  eapply step_det_loc1_loc2;eauto.
  eapply eff_loc1_memeqcorestep;eauto.
Qed.

Theorem SpecLang_wdFP: wdFP speclang.
Proof. apply wd_wdFP, SpecLang_wd. Qed.

Theorem SpecLang_det: lang_det speclang.
Proof. apply specLang_det. Qed.
