(** This file gives the definition of client module simulation, 
which is relation between low-level x86tso program calling object implementation, 
and high-level x86SC program calling object specification (Corresponding to the 
[Definiton 33] in submission #115 supplemental text)
 *)
Require Import Coqlib Maps.
Require Import AST Integers Floats Values Events Globalenvs Smallstep.

Require Import CUAST.

Require Import Footprint GMemory TSOMem FMemOpFP.
Require Import GlobDefs GAST ETrace LDSimDefs.

Require Import ASM_local AsmLang AsmTSO TSOGlobSem.
Require Import InteractionSemantics.
Require Export RGRels.

Local Notation footprint := FP.t.

(** Client footprint conflict with buffer of other threads *)
(** TODO: move to ? *)

Definition conflict_bi (fp: footprint) (bi: buffer_item) : Prop :=
  FP.conflict fp (bi_footprint bi).

(** Corresponding to the definition of [conflict_c] in Figure 20 in submission #115
supplemental text *)
Inductive conflictc 
          (t: tid) (fp: footprint) (B: buffers): Prop :=
| Conflictc: forall bi t',
    t' <> t ->
    In bi (B t') ->
    conflict_bi fp bi ->
    conflictc t fp B.

    
(** relation between client src/tgt footprints, for reordering *)
Definition fpmatchc (sfp tfp: footprint): Prop := FP.subset tfp sfp.

(** * Client module simulation *)
Section ClientSim.

  Variable Rc: tid -> stRel.
  Variable Gc: tid -> stRel.
  Variable Ic: stInv.

  (** List the properties of client simulation *)
  Record clientsim_properties
         {sl: Language}
         (sG: G sl)
         (sge: Genv.t (F sl) (V sl))
         (tge: genv)
         (match_state: tid -> (core sl * gmem) -> (AsmTSO.core * tsomem) -> Prop): Prop :=
    {
      match_init:
         forall id args tc,
           AsmTSO.init_core tge id args = Some tc ->
           exists sc,
             init_core sl sG id args = Some sc /\
             (forall t sm tm,
                 Ic sm tm ->
                 sep_obj_client_block sm ->
                 match_state t (sc, sm) (tc, tm))
      ;

      match_init_none:
        forall id args,
          AsmTSO.init_core tge id args = None ->
          init_core sl sG id args = None
      ;

      match_tau:
        forall t sc sm tc tm fl b m tfp tc' b' m',
          match_state t (sc, sm) (tc, tm) ->
          tso_buffers tm t = b ->
          memory tm = m ->
          tm_alloc_not_fl tm fl t -> rel_tm_gm_vb sm tm fl t ->
          tsostep tge fl tc (b, m) tfp tc' (b', m') ->
          let tm' := (mktsomem (tupdate t b' (tso_buffers tm)) m') in
          (* normal step *)
          (exists sfp sc' sm',
              step sl sG fl sc sm sfp sc' sm'
              /\ ((* no conflict *)
                (~ conflictc t tfp (tso_buffers tm)
                 /\ fpmatchc sfp tfp
                 /\ Gc t sm tm sm' tm'
                 /\ match_state t (sc', sm') (tc', tm')
                 /\ tm_alloc_not_fl tm' fl t
                 /\ rel_tm_gm_vb sm' tm' fl t)
                \/
                (* conflict *)
                (conflictc t tfp (tso_buffers tm)
                 /\ fpmatchc sfp tfp)
              )
          )
          \/
          (* sc abort *)
          (forall FP sc'' sm'', ~ step sl sG fl sc sm FP sc'' sm'')
      ;

      match_at_external:
        forall t sc sm tc tm,
          match_state t (sc, sm) (tc, tm) ->
          AsmTSO.at_external tge tc = at_external sl sG sc
      ;
      
      match_after_external:
        forall t sc sm tc tm ores tc', 
          match_state t (sc, sm) (tc, tm) ->
          AsmTSO.after_external tc ores = Some tc' ->
          exists sc', after_external sl sc ores = Some sc'
                 /\ match_state t (sc', sm) (tc', tm)
      ;

      match_after_external_none:
        forall t sc sm tc tm ores,
          match_state t (sc, sm) (tc, tm) ->
          AsmTSO.after_external tc ores = None ->
          after_external sl sc ores = None
      ;
      
      match_halted:
        forall t sc sm tc tm,
          match_state t (sc, sm) (tc, tm) ->
          AsmTSO.halt tc = halt sl sc
      ;
       
      
      match_abort:
        forall t sc sm tc tm fl m,
          match_state t (sc, sm) (tc, tm) ->
          tm_alloc_not_fl tm fl t -> rel_tm_gm_vb sm tm fl t ->
          (forall t', tso_buffers tm t' = nil) ->
          memory tm = m ->
          (forall fp tc' b' m',
              ~ (tsostep tge fl tc (nil, m) fp tc' (b', m') /\
                 exists m'', apply_buffer b' m' = Some m'')) ->
          (forall FP sc' sm', ~ step sl sG fl sc sm FP sc' sm')
          \/ (forall fm, ~ FMemory.embed m fl fm)
      ;

      match_abort_after_external:
        forall t sc sm tc tm ores,
          match_state t (sc, sm) (tc, tm) ->
          AsmTSO.after_external tc ores = None ->
          after_external sl sc ores = None
      ;

      match_rely:
        forall t sc sm tc tm sm' tm',
          match_state t (sc, sm) (tc, tm) ->
          Rc t sm tm sm' tm' ->
          sep_obj_client_block sm' ->
          match_state t (sc, sm') (tc, tm')
      ;

      match_no_entatom:
        forall t sc sm tc tm fnid sg args,
          match_state t (sc, sm) (tc, tm) ->
          at_external sl sG sc = Some (fnid, sg, args) ->
          fnid <> ent_atom
          /\ fnid <> ext_atom
      ;
          

    }.
  
End ClientSim.

(** Client module simulation (corresponding to the [Defintion 33] in 
submission #115 supplemental text)  *)
Definition clientsim
           (Rc Gc: tid -> stRel) (Ic: stInv)
           (sl: Language)
           (scu: comp_unit sl)
           (tcu: AsmTSO.comp_unit) : Prop :=
  forall sge sG tge,
    init_genv sl scu sge sG ->
    AsmTSO.init_genv tcu tge ->
    genv_match _ _ sge tge ->
    exists match_state,
      clientsim_properties Rc Gc Ic sG sge tge match_state.








(** * R/G/I for client modules *)
(** TODO: move to GMemory.v *)
Lemma unchanged_on_sym:
  forall P gm gm',
    GMem.unchanged_on P gm gm' ->
    GMem.unchanged_on P gm' gm.
Proof.
  intros. destruct H. constructor.
  intros. firstorder.
  intros. apply iff_sym. apply unchanged_on_perm; auto. eapply unchanged_on_validity; eauto.
  intros. symmetry. apply unchanged_on_contents. auto. apply unchanged_on_perm; auto.
  eapply unchanged_on_validity; eauto.
  unfold GMem.valid_block. destruct (in_dec peq b (GMem.validblocks gm')); auto.
  eapply GMem.invalid_noaccess in n.
  unfold GMem.perm in H0. rewrite n in H0. inversion H0.
Qed.

(** Client invariant [Ic] *)
Definition buf_alloc_invalid (tm: tsomem) : Prop :=
  forall t b lo hi,
    In (BufferedAlloc b lo hi) (tso_buffers tm t) ->
    ~ GMem.valid_block (memory tm) b.

Definition buf_alloc_norep (tm: tsomem) : Prop :=
  forall t t' i j b lo hi lo' hi',
    List.nth_error (tso_buffers tm t) i = Some (BufferedAlloc b lo hi) ->
    List.nth_error (tso_buffers tm t') j = Some (BufferedAlloc b lo' hi') ->
    t = t' /\ i = j.

Record Ic (sm: gmem) (tm: tsomem) : Prop :=
  {
    Ic_ub_safe:
      unbuffer_safe tm
    ;

    Ic_no_conflict_bi:
      forall b ofs t1 t2,
        t1 <> t2 ->
        ~ obj_mem sm b ofs ->
        in_buffer (tso_buffers tm t1) b ofs ->
        in_buffer (tso_buffers tm t2) b ofs ->
        False;
      
    Ic_mem_eq:
      forall t tgm',
        apply_buffer (tso_buffers tm t) (memory tm) = Some tgm' ->
        forall b ofs,
          ~ obj_mem sm b ofs ->
          (forall t', t' <> t -> ~ in_buffer (tso_buffers tm t') b ofs) ->
          eq_on_loc b ofs sm tgm'
    ;

    Ic_buf_alloc_invalid:
      buf_alloc_invalid tm;

    Ic_buf_alloc_norep:
      buf_alloc_norep tm;
  }.

(** Client rely [Rc] *)
Definition Rc (t: tid) (sm: gmem) (tm: tsomem) (sm': gmem) (tm': tsomem) : Prop :=
  Ic sm tm /\ Ic sm' tm'.

(** Client guarantee [Gc] *)
Definition Gc (t: tid) (sm: gmem) (tm: tsomem) (sm': gmem) (tm': tsomem) : Prop :=
  Ic sm tm /\ Ic sm' tm'
  (* obj mem domain unchanged *)
  /\ (forall b ofs, obj_mem sm b ofs <-> obj_mem sm' b ofs)
  (* obj mem content/perm unchanged *)
  /\ (forall b ofs, obj_mem sm b ofs -> eq_on_loc b ofs sm sm')
  (* tso memory unchanged *)
  /\ memory tm = memory tm'
  (* tso buffer inserted only client locations *)
  /\ (exists bis, tso_buffers tm' = tupdate t (tso_buffers tm t ++ bis) (tso_buffers tm)
     /\
     (forall b ofs, in_buffer bis b ofs ->
                    (~ obj_mem sm b ofs (*/\ exists k p, GMem.perm sm' b ofs k p*))))
     /\ GMem.forward sm sm'.

(** Client invariant [Ic] implies [unbuffer_safe] *)
Lemma Ic_unbuffer_safe:
  forall sm tm,
    Ic sm tm -> unbuffer_safe tm.
Proof. intros. inv H; auto. Qed.

(** [Ic] is stable under step [Gc] *)
Lemma Ic_sta:
  forall t : tid, Sta Ic (Gc t).
Proof.
  unfold Sta. intros. unfold Gc in H0. tauto.
Qed.

(** [Gc] ==> [Rc] *)
Lemma Gc_implies_Rc:
  forall t t' : tid, Implies (Gc t) (Rc t').
Proof.
  unfold Implies. intros.
  unfold Gc, Rc in *. tauto.
Qed.

(** [Ic] is stable under unbuffer step *)

Lemma unbuffer_safe_apply_buffer :
  forall bfs t m,
    unbuffer_safe {| tso_buffers := bfs; memory := m |} ->
    exists m', apply_buffer (bfs t) m = Some m'.
Proof.
  intros bfs t.
  remember (bfs t) as bf.
  generalize dependent bfs.
  generalize dependent t.
  induction bf; intros.
  { simpl; eauto. }
  { inversion H; subst; simpl in *.
    exploit ABIS. eauto. intros [m' Happly_buffer_item].
    rewrite Happly_buffer_item; simpl.
    eapply (IHbf t (tupdate t bf bfs)).
    unfold tupdate. destruct peq; auto; contradiction.
    eapply UNBS; eauto.
  }
Qed.

Lemma eq_on_loc_trans:
  forall b ofs m1 m2 m3,
    eq_on_loc b ofs m1 m2 ->
    eq_on_loc b ofs m2 m3 ->
    eq_on_loc b ofs m1 m3.
Proof.
  intros. inv H; inv H0; constructor; try congruence.
  rewrite eq_loc_validity. auto.
  intro. rewrite eq_loc_perm. auto.
Qed.

Lemma eq_on_loc_sym:
  forall b ofs m1 m2,
    eq_on_loc b ofs m1 m2 -> eq_on_loc b ofs m2 m1.
Proof.
  intros. inv H; constructor; auto. tauto.
Qed.

Lemma app_eq_length_eq_inj:
  forall A (l1 l2 l1' l2': list A),
    length l1 = length l1' ->
    l1 ++ l2 = l1' ++ l2' ->
    l2 = l2'.
Proof.
  induction l1.
  { destruct l1'; simpl. auto. discriminate. }
  { destruct l1'; simpl. discriminate.
    intros. inv H. inv H0. eapply IHl1. eauto. auto. }
Qed.
  
Lemma apply_buffer_item_eq_on_loc_preserve:
  forall bi gm1 gm2 b ofs gm1' gm2',
    eq_on_loc b ofs gm1 gm2 ->
    apply_buffer_item bi gm1 = Some gm1' ->
    apply_buffer_item bi gm2 = Some gm2' ->
    eq_on_loc b ofs gm1' gm2'.
Proof.
  intros. destruct bi; simpl in *; inv H0; inv H1.
  { (* alloc *)
    destruct (eq_block b0 b); [subst|].
    { constructor; simpl; repeat rewrite PMap.gss; try tauto.
      unfold GMem.valid_block. simpl. inv H; tauto. }
    { constructor; simpl; repeat rewrite PMap.gso; inv H; auto.
      unfold GMem.valid_block. simpl. tauto. }
  }
  { (* free *)
    unfold free, unchecked_free in *.
    destruct range_perm_dec; inv H3.
    destruct range_perm_dec; inv H2.
    destruct (eq_block b b0); [subst|].
    { constructor; unfold GMem.valid_block; simpl; repeat rewrite PMap.gss; simpl; inv H; try tauto.
      intro. rewrite eq_loc_perm. auto. }
    { constructor; unfold GMem.valid_block; simpl; repeat rewrite PMap.gso; simpl; inv H; try tauto. }
  }
  { (* store *)
    unfold store in *.
    destruct valid_access_dec; inv H3.
    destruct valid_access_dec; inv H2.
    destruct (eq_block b b0); [subst|].
    { constructor; unfold GMem.valid_block; simpl; repeat rewrite PMap.gss; simpl; inv H; try tauto.
      destruct (Classical_Prop.classic (z <= ofs < z + Z.of_nat (length (Memdata.encode_val m v)))).
      { enough (FMemory.Mem.getN (length (Memdata.encode_val m v)) z
                                 (FMemory.Mem.setN  (Memdata.encode_val m v) z (GMem.mem_contents gm1) !! b0) =
                FMemory.Mem.getN (length (Memdata.encode_val m v)) z
                                 (FMemory.Mem.setN  (Memdata.encode_val m v) z (GMem.mem_contents gm2) !! b0)).
        { revert H H0. clear. generalize (Memdata.encode_val m v). intros.
          assert (exists n, ofs = z + (Z.of_nat n) /\ (n < length l)%nat) as [n [Hofs Hn]].
          { exists (Z.to_nat (ofs - z)). split. rewrite Z2Nat.id; Lia.lia.
            apply Nat2Z.inj_lt. rewrite Z2Nat.id; Lia.lia. }
          subst ofs. destruct H. clear H1.
          assert (exists n', n + S n' = length l)%nat as [n' Hlength].
          { exists (length l - n - 1)%nat. Lia.lia. }
          rewrite <- Hlength in *. repeat rewrite FMemory.Mem.getN_concat in H0.
          apply app_eq_length_eq_inj in H0.
          simpl in H0. inv H0. auto.
          do 2 rewrite FMemory.Mem.getN_length. auto.
        }
        repeat rewrite FMemory.Mem.getN_setN_same; auto.
      }
      { repeat rewrite FMemory.Mem.setN_outside; auto; Lia.lia. }
    }
    { constructor; unfold GMem.valid_block; simpl; repeat rewrite PMap.gso; simpl; auto; inv H; try tauto. }
  }
Qed.
  
Lemma apply_buffer_eq_on_loc_preserve:
  forall buf gm1 gm2 b ofs gm1' gm2',
    eq_on_loc b ofs gm1 gm2 ->
    apply_buffer buf gm1 = Some gm1' ->
    apply_buffer buf gm2 = Some gm2' ->
    eq_on_loc b ofs gm1' gm2'.
Proof.
  induction buf; simpl; intros; inv H0; inv H1; auto.
  destruct (apply_buffer_item a gm1) eqn:?H; inv H3.
  destruct (apply_buffer_item a gm2) eqn:?H; inv H2.
  exploit apply_buffer_item_eq_on_loc_preserve; eauto.
Qed.

Lemma apply_buffer_item_eq_on_loc_other:
  forall bi gm gm' b ofs,
    apply_buffer_item bi gm = Some gm' ->
    ~ in_buffer_item bi b ofs ->
    eq_on_loc b ofs gm gm'.
Proof.
  intros. destruct bi; simpl in *; inv H.
  { (* alloc *)
    destruct (eq_block b0 b). exfalso. apply H0. subst. constructor.
    constructor; simpl.
    { unfold GMem.valid_block. simpl. split; auto. intros [C|H]; auto; contradiction. }
    { intros. rewrite PMap.gso; auto. }
    { intros. rewrite PMap.gso; auto. }
  }
  { (* free *)
    unfold free in H2. destruct range_perm_dec; inv H2.
    unfold unchecked_free.
    destruct (eq_block b0 b). subst.
    destruct (Classical_Prop.classic (z <= ofs < z0)). exfalso. apply H0. constructor. auto.
    { constructor; simpl.
      { unfold GMem.valid_block. split; auto. }
      { intros. rewrite PMap.gss. destruct zle, zlt; simpl; auto. Lia.lia. }
      { auto. }
    }
    { constructor; simpl.
      { unfold GMem.valid_block. simpl. split; auto. }
      { intros. rewrite PMap.gso; auto. }
      { auto. }
    }
  }
  { (* store *)
    unfold store in H2. destruct valid_access_dec; inv H2.
    destruct (eq_block b0 b). subst.
    destruct (Classical_Prop.classic (z <= ofs < z + Z.of_nat (length (Memdata.encode_val m v)))).
    exfalso. eapply H0. constructor. rewrite Memdata.size_chunk_conv.
    assert (length (Memdata.encode_val m v) = Memdata.size_chunk_nat m).
    { clear. destruct m; simpl; unfold Memdata.encode_val, Memdata.size_chunk_nat;
               destruct v; try rewrite length_list_repeat; auto. }
    Lia.lia.
    { constructor; simpl.
      { unfold GMem.valid_block. split; auto. }
      { intros. auto. }
      { rewrite PMap.gss. rewrite FMemory.Mem.setN_outside. auto. Lia.lia. }
    }
    { constructor; simpl.
      { unfold GMem.valid_block. split; auto. }
      { intros. auto. }
      { rewrite PMap.gso; auto. }
    }
  }
Qed.

Lemma apply_buffer_eq_on_loc_other:
  forall buf gm gm' b ofs,
    apply_buffer buf gm = Some gm' ->
    ~ in_buffer buf b ofs ->
    eq_on_loc b ofs gm gm'.
Proof.
  induction buf. intros. simpl in *. inv H. constructor; tauto.
  intros. simpl in H. destruct apply_buffer_item eqn:?H; inv H.
  eapply apply_buffer_item_eq_on_loc_other in H1.
  eapply eq_on_loc_trans. eauto. eapply IHbuf; eauto.
  intro C. inv C. apply H0. econstructor; simpl; eauto.
  intro C. apply H0. econstructor; simpl; eauto.
Qed.

Lemma Ic_buf_alloc_invalid_norep_stable:
  forall tm t tm',
    buf_alloc_invalid tm ->
    buf_alloc_norep tm ->
    unbuffer tm t = Some tm' ->
    buf_alloc_invalid tm' /\ buf_alloc_norep tm'.
Proof.
  intros tm t tm' Ic_buf_alloc_invalid Ic_buf_alloc_norep H.
  unfold unbuffer in H. destruct tso_buffers eqn:A. discriminate.
  destruct apply_buffer_item eqn:B; inv H.
  unfold buf_alloc_invalid, buf_alloc_norep. split.
  { intros. destruct b; simpl in *; unfold tupdate, GMem.valid_block in *. 
    { destruct peq.
      { subst. eapply In_nth_error in H. destruct H as (N & Hbi). intro.
        unfold alloc in B. inv B. simpl in H. destruct H.
        subst. exploit (Ic_buf_alloc_norep t t 0%nat (S N)); try rewrite A; simpl; eauto. intuition.
        exploit (Ic_buf_alloc_invalid); try rewrite A; simpl; try right; eauto.
        eapply nth_error_In; eauto. }
      { unfold alloc in B. inv B. simpl. intro. destruct H0.
        eapply In_nth_error in H. destruct H as (N & Hbi).
        { subst. exploit (Ic_buf_alloc_norep t t0 0%nat N); try rewrite A; simpl; eauto; intuition. }
        { eapply Ic_buf_alloc_invalid; eauto. }
      }
    }
    { unfold free in B. destruct range_perm_dec; inv B. simpl.
      destruct peq; subst.
      eapply Ic_buf_alloc_invalid. eauto. rewrite A. right. eauto.
      eapply Ic_buf_alloc_invalid. eauto. 
    }
    { unfold store in B. destruct valid_access_dec; inv B. simpl.
      destruct peq; subst.
      eapply Ic_buf_alloc_invalid. eauto. rewrite A. right. eauto.
      eapply Ic_buf_alloc_invalid. eauto. 
    }
  } 
  { simpl. intros. unfold tupdate in *.
    destruct peq; subst.
    destruct peq; subst.
    split. auto. exploit (Ic_buf_alloc_norep t t (S i) (S j)); try rewrite A; eauto; intuition.
    exfalso. apply n. exploit (Ic_buf_alloc_norep t t' (S i) j); try rewrite A; eauto; intuition.
    destruct peq; subst.
    exfalso. apply n. exploit (Ic_buf_alloc_norep t0 t i (S j)); try rewrite A; eauto; intuition.
    eapply Ic_buf_alloc_norep; eauto.
  }
Qed.
          
Lemma UBSta_Ic:
  UBSta Ic.
Proof.
  unfold UBSta. intros gm tm gm' tm' HIc [A [t Hunbuf]]. subst gm'.
  unfold unbuffer in Hunbuf. destruct (tso_buffers tm t) eqn:A; inv Hunbuf.
  destruct (apply_buffer_item b (memory tm)) eqn:B; inv H0.
  rename g into tgm'.
  constructor.
  { apply Ic_ub_safe in HIc. inv HIc. eapply UNBS; eauto. }
  { simpl. intros b1 ofs t1 t2 Ht. unfold tupdate.
    destruct peq. destruct peq. congruence.
    intros. eapply Ic_no_conflict_bi. eauto. eauto. eauto. eauto. rewrite A.
    inv H0. econstructor. simpl. right. eauto. auto.
    destruct peq.
    intros. eapply Ic_no_conflict_bi. eauto. eauto. eauto. eauto. rewrite A.
    inv H1. econstructor. simpl. right. eauto. auto.
    eapply Ic_no_conflict_bi; eauto. }
  { simpl. unfold tupdate in *. intros. destruct peq.
    { (* t = t0 *)
      subst. eapply Ic_mem_eq. eauto. rewrite A. simpl. rewrite B. simpl. auto. auto.
      intros. specialize (H1 t' H2). destruct peq; auto. }
    { (* t <> t0 *)
      rename t into t_unbuffer.
      unfold alloc in H. inv H. simpl.
      assert (forall b' ofs', ~ in_buffer_item b b' ofs' -> eq_on_loc b' ofs' (memory tm) tgm').
      { intros. eapply apply_buffer_item_eq_on_loc_other; eauto. }
      destruct (Classical_Prop.classic (forall t', t' <> t0 -> ~ in_buffer (tso_buffers tm t') b1 ofs)).
      { (* not in buffer_item b *)
        assert (~ in_buffer_item b b1 ofs).
        { intro C. eapply H2. eauto. rewrite A. econstructor. left. eauto. eauto. }
        assert (exists tgm0, apply_buffer (tso_buffers tm t0) (memory tm) = Some tgm0) as [tgm0 Happly0].
        { eapply unbuffer_safe_apply_buffer. destruct tm. inv HIc. auto. }
        eapply H in H4. eapply Ic_mem_eq in HIc; try exact Happly0; eauto. clear H. clear B.
        exploit apply_buffer_eq_on_loc_preserve. exact H4. eauto. eauto. clear H4. intro.
        eapply eq_on_loc_trans; eauto. 
      }
      { (* in buffer_item b *)
        assert (in_buffer_item b b1 ofs).
        { apply Classical_Pred_Type.not_all_ex_not in H2. destruct H2 as [t'' H2].
          apply Classical_Prop.imply_to_and in H2. destruct H2 as [Ht'' H2].
          apply Classical_Prop.imply_to_and in H2. destruct H2 as [H2 _].
          destruct (peq t'' t_unbuffer).
          subst t''. rewrite A in H2. inv H2.
          destruct H4; subst; auto.
          exfalso. eapply H1. eauto. destruct peq; try contradiction. econstructor; eauto.
          exfalso. eapply H1. exact Ht''. destruct peq. contradiction. auto.
        }
        assert (forall t', t' <> t_unbuffer -> ~ in_buffer (tso_buffers tm t') b1 ofs).
        { intros. intro C. inv C.
          eapply Ic_no_conflict_bi in HIc; eauto.
          econstructor; eauto. rewrite A. econstructor; simpl; eauto.
        }
        assert (exists tgm_unbuffer, apply_buffer b0 tgm' = Some tgm_unbuffer) as
            [tgm_unbuffer Happly_unbuffer].
        { apply Ic_unbuffer_safe in HIc. destruct tm; simpl in *.
          exploit unbuffer_safe_apply_buffer. eauto.
          intros [tgm_unbuffer Happly]. rewrite A in Happly. simpl in Happly.
          rewrite B in Happly. simpl in Happly. eauto. }
        assert (eq_on_loc b1 ofs tgm' tgm_unbuffer).
        { eapply apply_buffer_eq_on_loc_other. eauto. intro. eapply H1. eauto. destruct peq; auto; contradiction. }
        assert (eq_on_loc b1 ofs tgm'0 tgm').
        { apply eq_on_loc_sym. eapply apply_buffer_eq_on_loc_other. eauto. intro C.
          eapply Ic_no_conflict_bi in HIc; eauto. rewrite A. econstructor; simpl; eauto. }
        assert (eq_on_loc b1 ofs gm tgm_unbuffer).
        { eapply Ic_mem_eq; eauto. rewrite A. simpl. rewrite B. simpl. auto. }
        eapply eq_on_loc_trans. eauto.
        apply eq_on_loc_sym. eapply eq_on_loc_trans; eauto.
      }
    }
  }
  { unfold buf_alloc_invalid. intros. destruct b; simpl in *; unfold tupdate, GMem.valid_block in *. 
    { destruct peq.
      { subst. eapply In_nth_error in H. destruct H as (N & Hbi). intro.
        unfold alloc in B. inv B. simpl in H. destruct H.
        subst. exploit (Ic_buf_alloc_norep _ _ HIc t t 0%nat (S N)); try rewrite A; simpl; eauto. intuition.
        exploit (Ic_buf_alloc_invalid); try rewrite A; simpl; try right; eauto.
        eapply nth_error_In; eauto. }
      { unfold alloc in B. inv B. simpl. intro. destruct H0.
        eapply In_nth_error in H. destruct H as (N & Hbi).
        { subst. exploit (Ic_buf_alloc_norep _ _ HIc t t0 0%nat N); try rewrite A; simpl; eauto; intuition. }
        { eapply Ic_buf_alloc_invalid; eauto. }
      }
    }
    { unfold free in B. destruct range_perm_dec; inv B. simpl.
      destruct peq; subst.
      eapply Ic_buf_alloc_invalid. eauto. rewrite A. right. eauto.
      eapply Ic_buf_alloc_invalid. eauto. eauto.
    }
    { unfold store in B. destruct valid_access_dec; inv B. simpl.
      destruct peq; subst.
      eapply Ic_buf_alloc_invalid. eauto. rewrite A. right. eauto.
      eapply Ic_buf_alloc_invalid. eauto. eauto.
    }
  } 
  { unfold buf_alloc_norep.
    simpl. intros. unfold tupdate in *.
    destruct peq; subst.
    destruct peq; subst.
    split. auto. exploit (Ic_buf_alloc_norep _ _ HIc t t (S i) (S j)); try rewrite A; eauto; intuition.
    exfalso. apply n. exploit (Ic_buf_alloc_norep _ _ HIc t t' (S i) j); try rewrite A; eauto; intuition.
    destruct peq; subst.
    exfalso. apply n. exploit (Ic_buf_alloc_norep _ _ HIc t0 t i (S j)); try rewrite A; eauto; intuition.
    eapply Ic_buf_alloc_norep; eauto.
  }
Qed.  

Lemma UBImplies_Rc:
  forall t : tid, UBImplies Ic (Rc t).
Proof.
  unfold UBImplies. intros t gm tm gm' tm' HIc HUB.
  exploit UBSta_Ic; eauto. destruct HUB. subst. unfold Rc. tauto.
Qed.




Lemma nth_error_split':
  forall A (l ls:list A) i a,
    nth_error (l++ls) i = Some a ->
    nth_error l i = Some a \/ ( nth_error ls (i-(length l)) = Some a /\ (i >= length l)%nat).
Proof.
  induction l;simpl;intros.
  right;eauto. assert((i-0)%nat=i). Lia.lia.
  split;auto.
  congruence.
  Lia.lia.

  destruct i. simpl in H. inv H.
  left. auto.
  simpl in H. eapply IHl in H as [|[]].
  left;eauto. right;split;auto. Lia.lia.
Qed.
Lemma nth_error_nil:
  forall A i,
    @nth_error A nil i = None.
Proof.
  induction i;auto.
Qed.
Lemma nth_error_cons_nil:
  forall A (bi bi':A) i,
    nth_error (bi::nil) i = Some bi' ->
    i = 0%nat /\ bi = bi'.
Proof.
  intros. destruct i;inv H;auto.
  pose proof nth_error_nil A i. congruence.
Qed.

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
         end;try congruence.
Local Ltac ex_match2:=
  repeat match goal with
         | H: context[match ?x with _ => _ end]  |- _ => destruct x eqn:?Hx; try discriminate
         | H: _ |- context[match ?x with _ => _ end ] => destruct x eqn:?Hx;try discriminate
         end;try congruence;try contradiction.
Local Ltac ex_match3:=
  match goal with
    H: ?x = ?y |- context [?x] => rewrite H
  end.

Ltac solve_nth_error:=
  match goal with
  | H: nth_error (?x::nil) ?y = Some ?z |- _
    => eapply nth_error_cons_nil in H;Hsimpl;subst;
      match goal with
      | H : x = z |- _ => inv H
      end
  | H: nth_error (?l++?ls) ?i = Some ?a |- _ =>
    apply nth_error_split' in H as [|[]]
  end.
Ltac esolve_nth_error:=
  repeat solve_nth_error;subst;eauto.
Lemma alloc_norep_preserve:
  forall bufs m,
    buf_alloc_norep (mktsomem bufs m)->
    forall bi,
      match bi with
      |BufferedAlloc b0 lo0 hi0 =>
       forall t b lo hi, In (BufferedAlloc b lo hi)(bufs t) -> b <> b0
      |_ => True
      end ->
      forall t m',
        buf_alloc_norep (mktsomem (tupdate t (bufs t ++ (bi::nil)) bufs) m').
Proof.
  destruct bi;unfold buf_alloc_norep,tupdate;simpl;intros.
  {
    assert(R:forall (t : tid) (b0 : block) (lo hi : Z) i,
              nth_error (bufs t) i = Some (BufferedAlloc b0 lo hi) -> b0 <> b).
    intros. eapply H0;eauto. eapply nth_error_In;eauto.
    clear H0;rename R into H0.
    ex_match2;subst;eauto;esolve_nth_error.
    apply H0 in H2;congruence.
    apply H0 in H1;congruence.
    split;auto. Lia.lia.
    apply H0 in H1;congruence.
    apply H0 in H2;congruence.
  }
  ex_match2; esolve_nth_error.
  ex_match2; esolve_nth_error.
Qed.