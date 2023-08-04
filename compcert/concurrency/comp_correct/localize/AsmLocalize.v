Require Import Coqlib Maps Integers Values Memdata AST Globalenvs.
Require Import Blockset Footprint FMemOpFP GMemory FMemory FMemPerm MemAux CUAST
        Asm AsmLang ASM_local LDSimDefs Localize ValRels MemInterpolant val_casted.

Lemma init_genv_iff: forall cu ge G,
    AsmLang.init_genv cu ge G <->
    G = ge /\ ge_related ge (Genv.globalenv (mkprogram (cu_defs cu) (cu_public cu) 1%positive)).
Proof. intros. unfold AsmLang.init_genv. tauto. Qed.

Lemma Loclocalize_univ:
  forall j, Loclocalize j Locs.univ Locs.univ.
Proof. intros. constructor. intros. tauto. Qed.

Lemma Loclocalize_emp:
  forall j, Loclocalize j Locs.emp Locs.emp.
Proof. intros. constructor. intros. tauto. Qed.

Lemma FPlocalize_cmp_undef:
  forall j, FPlocalize j
                  {| FP.cmps := Locs.univ; FP.reads := Locs.emp; FP.writes := Locs.emp; FP.frees := Locs.emp |}
                  {| FP.cmps := Locs.univ; FP.reads := Locs.emp; FP.writes := Locs.emp; FP.frees := Locs.emp |}.
Proof. constructor; simpl; auto using Loclocalize_emp, Loclocalize_univ. Qed.


Lemma invert_symbol_from_string_eq:
  forall F V (ge ge_local: Genv.t (AST.fundef F) V) (NOREPEF: norep_ef_name ge_local),
    (forall b gd, (Genv.genv_defs ge_local) ! b = Some gd -> exists id, (Genv.genv_symb ge_local) ! id = Some b) ->
    ge_related ge ge_local ->
    forall name, invert_symbol_from_string ge name = invert_symbol_from_string ge_local name.
Proof.
  intros. unfold invert_symbol_from_string.
  exploit invert_block_from_string_eq; eauto. intro. inv H1.
  rewrite <- H3, <- H4. auto.
  simpl in *. rewrite <- H3, <- H2.
  destruct H4 as [id [FIND FIND']].
  do 2 (erewrite Genv.find_invert_symbol; eauto).
Qed.

(** maybe could be generalized to any Genv.t? need a generalize version of init_mem *)
Program Definition empmem (BOUND: block) : Memory.Mem.mem :=
  Memory.Mem.mkmem (PMap.init (ZMap.init Undef))
                   (PMap.init (fun (_ : Z) (_ : Memtype.perm_kind) => None))
                   (BOUND) _ _ _.
Next Obligation. rewrite PMap.gi. constructor. Qed.
Next Obligation. rewrite PMap.gi. auto. Qed.
Next Obligation. rewrite PMap.gi. auto. Qed.

Lemma strip_valid_block: forall fm, (GMem.valid_block (strip fm) = Mem.valid_block fm).
Proof. destruct fm; auto. Qed.

Lemma strip_mem_access: forall fm, GMem.mem_access (strip fm) = Mem.mem_access fm.
Proof. destruct fm. auto. Qed.

Lemma strip_mem_contents: forall fm, GMem.mem_contents (strip fm) = Mem.mem_contents fm.
Proof. destruct fm; auto. Qed.
Lemma list_forall2_split:
  forall A B (P: A -> B -> Prop) (al' bl': list B) (l: list A),
    list_forall2 P l (al' ++ bl') ->
    exists al bl, l = al ++ bl /\ list_forall2 P al al' /\ list_forall2 P bl bl'.
Proof.
  induction al'; intros; simpl. exists nil, l. split; auto. split. constructor. auto.
  simpl in H. inv H. apply IHal' in H4. destruct H4 as [al0 [bl [SPLIT [P1 P2]]]].
  rewrite SPLIT. exists (a1 :: al0), bl. split. auto. split. constructor; auto. auto.
Qed.
Lemma lmem_construction:
  forall F V (ge ge_local: Genv.t F V) j m fl,
    Bset.inject j (fun b => Plt b (Genv.genv_next ge_local)) (fun b => Plt b (Genv.genv_next ge)) ->
    ge_match_strict j ge ge_local ->
    init_gmem_generic ge m ->
    norep fl ->
    no_overlap fl (valid_block_bset m) ->
    exists lm, init_mem_generic ge_local lm /\
          mem_related j (Genv.genv_next ge) fl m lm.
Proof.
  intros F V ge ge_local j m fl INJECT GEMATCH INITMEM NOREP NOOVERLAP.
  erewrite <- (ge_match_strict_next _ ge ge_local) in INJECT ; eauto.
  exploit bset_inject_revert; eauto.
  intros (j' & INJECT' & CONSIST).
  pose (Genv.genv_next ge) as BOUND.
  assert (SHARED_VALID: forall b b', j b = Some b' -> Plt b (Memory.Mem.nextblock (empmem BOUND))).
  { subst BOUND. unfold empmem. simpl. intros. eapply Bset.inj_dom' in H; eauto using Bset.inj_weak. auto. }
  exists (inject_memory j j' BOUND m (empmem BOUND) CONSIST SHARED_VALID).
  destruct INITMEM as [fm [STRIP INITMEM]]. subst m.
  match goal with |- _ /\ ?x => assert x end.
  { econstructor; eauto.
    (* no overlap *)
    intro. inv INITMEM. rewrite dom_match_fm. unfold valid_block_bset in NOOVERLAP.
    destruct fm; unfold strip, Mem.valid_block, GMem.valid_block, get_block in *; simpl in *.
    eapply NOOVERLAP. eauto.
    (* valid block *)
    intros. unfold inject_memory, Memory.Mem.valid_block; simpl.
    subst BOUND. rewrite strip_valid_block. erewrite <- dom_match_fm; eauto.
    unfold construct_inj in H. destruct (plt b). eapply Bset.inj_range' in H; eauto using Bset.inj_weak. tauto.
    split; intro; try contradiction. exfalso. inv H. eapply NOOVERLAP; eauto.
    unfold Bset.belongsto, valid_block_bset, strip, GMem.valid_block; simpl.
    eapply dom_match_fm; eauto.
    (* shared valid global *)
    intros. unfold GMem.valid_block, strip; simpl. eapply dom_match_fm; eauto.
    (* eq perm *)
    unfold inject_memory. 
    intros. unfold construct_inj in H. 
    unfold Memory.Mem.perm, Memory.Mem.perm_order'. simpl.      
    destruct (proj2_sig (inject_access_c j j' BOUND (PMap.init (fun _ _ => None)) (Mem.mem_access fm))).
    simpl in *. rewrite (H3 b). unfold inject_access.
    destruct plt. rewrite H.
    (* * b < bound, shared eq to gm' *)
    erewrite eq_perm_kind_convert; eauto.
    erewrite <- (eq_permission_convert' P P'); eauto.
    unfold GMem.perm, Memperm.perm_order'. rewrite strip_mem_access.
    destruct ((Mem.mem_access fm)!!b' ofs K') eqn:? ; simpl.
    apply perm_order_convert'_eq. tauto.
    (* * b > bound, use unchg_local relate gm' and gm, then by related ... *)
    (* * invalid *)
    unfold GMem.perm, Memperm.perm_order'. rewrite strip_mem_access.
    rewrite PMap.gi. split; intro; try contradiction.
    rewrite Mem.invalid_noaccess in H4; auto.
    intro. eapply dom_match_fm in H5; eauto. inv H. eapply NOOVERLAP; eauto.
    unfold valid_block_bset. rewrite strip_valid_block. unfold Bset.belongsto.
    erewrite <- dom_match_fm. eauto. eauto.
    
    (* content eq*)
    unfold inject_memory, construct_inj. simpl.
    destruct (proj2_sig (inject_content_c j j' BOUND (PMap.init (ZMap.init Undef)) (Mem.mem_contents fm))).
    intros. simpl in *. rewrite (H0 b). unfold inject_content.
    destruct plt.
    (* * b < bound *)
    rewrite H1. destruct (proj2_sig (inject_zmap_memval_c j' (Mem.mem_contents fm) !! b')).
    rewrite H4. unfold inject_zmap_memval. unfold inject_memval.
    destruct (ZMap.get ofs (Mem.mem_contents fm) !! b') eqn:HFrag; try constructor.
    destruct v; simpl; try constructor.
    (* by reach_close, b0 in bound, thus exists b'0, j' b0 = b'0 *)
    inv INITMEM. destruct reach_closed_fm as [reach_closed_fm _ _]. exploit (reach_closed_fm b0).
    econstructor. instantiate (1:=((b',i)::nil)). econstructor; eauto. econstructor.
    unfold Bset.belongsto. rewrite <- dom_match_fm. exploit Bset.inj_range'; clear INJECT'; eauto using Bset.inj_weak.
    unfold Memory.Mem.perm in H2. simpl in H2.
    destruct (proj2_sig (inject_access_c j j' BOUND (PMap.init (fun _ _ => None)) (Mem.mem_access fm))).
    rewrite H6 in H2. unfold inject_access in H2. rewrite H1 in H2. destruct plt; [|xomega].
    generalize H2; clear; simpl; intros. 
    unfold GMem.perm, Memperm.perm_order''. rewrite strip_mem_access.
    destruct ((Mem.mem_access fm)!!b' ofs Memperm.Max);[|inv H2].
    destruct p; simpl; inv H2; constructor.
    unfold Bset.belongsto; intros.
    assert (exists b'0, j' b0 = Some b'0).
    { inv INJECT'. eapply dom_match_fm in H5. exploit Bset.inj_range; eauto. }
    destruct H6 as [b'0 H9].
    rewrite H9. econstructor. unfold Bset.inj_to_meminj. rewrite <- CONSIST in H9. rewrite H9.
    destruct plt. eauto.
    exfalso. apply n0. clear INJECT'. exploit Bset.inj_dom'; eauto using Bset.inj_weak.
    rewrite <- Integers.Ptrofs.unsigned_zero,
    Integers.Ptrofs.repr_unsigned, Integers.Ptrofs.add_zero. auto.
    (* * b >= bound *)
    exfalso.
    assert (in_fl fl b').
    { inv H1. unfold in_fl, get_block. eauto. }
    assert (construct_inj j BOUND fl b = Some b').
    { unfold construct_inj; destruct plt; [xomega|inv H1; auto]. }
    destruct (proj2_sig (inject_access_c j j' BOUND (PMap.init (fun _ _ => None)) (Mem.mem_access fm))).
    unfold Memory.Mem.perm in *. simpl in *.
    rewrite H6 in H2. unfold inject_access in H2. destruct plt; auto.
    rewrite PMap.gi in H2. inversion H2.
  }
  split; auto.
  { constructor.
    { (* globals initialized *)
      unfold Genv.globals_initialized. intros.
      inv INITMEM. clear reach_closed_fm. unfold globals_initialized_fmem in *.
      exploit (ge_match_strict_dom j ge ge_local); auto.
      intros [INJ _]. specialize (INJ b gd H0). destruct INJ as [b' INJ].
      pose proof (ge_match_strict_defs j ge ge_local GEMATCH b b' INJ) as A.
      unfold Genv.find_def in H0. rewrite H0 in A. inv A.
      rename x into gd', H1 into FIND', H0 into FIND, globdef_initialized_fm into GI'.
      assert (INJ':construct_inj j BOUND fl b = Some b').
      { unfold construct_inj. apply Genv.genv_defs_range in FIND.
        erewrite <- ge_match_strict_next in FIND; eauto. destruct plt; try contradiction; auto. }
      symmetry in FIND'. specialize (GI' b' gd' FIND'). inv H3.
      (* function *)
      { destruct GI' as [PERM0 PERMIFF0].
        split. eapply mem_related_mem_perm_eq; eauto. constructor. constructor.
        intros. specialize (PERMIFF0 ofs (perm_kind_convert k) (permission_convert p)).
        exploit PERMIFF0. eapply mem_related_mem_perm_eq in H0; eauto.
        unfold GMem.perm in H0. rewrite strip_mem_access in H0. eauto.
        apply perm_kind_convert_eq. apply permission_convert_eq. intros [? ?]. split; auto.
        destruct p; auto; inv H2. }
      (* var *)
      { destruct GI' as [RANGEPERM [PERMIFF [LOADSTORE LOADBYTES]]].
        inv H0; simpl in *. unfold Genv.perm_globvar in *. simpl in *.
        split.
        { (* perm *)
          unfold Memory.Mem.range_perm, Mem.range_perm in *. intros. apply RANGEPERM in H0.
          eapply mem_related_mem_perm_eq; eauto using perm_kind_convert_eq, permission_convert_eq. }
        split.
        { (* permiff *)
          intros. eapply mem_related_mem_perm_eq in H0; eauto using perm_kind_convert_eq, permission_convert_eq.
          unfold GMem.perm in H0. rewrite strip_mem_access in H0. eapply PERMIFF in H0. destruct H0.
          split. auto. generalize H1; clear. intro. destruct fro, fvo, p; inv H1; simpl; try constructor. }
        split.
        { (* load store *)
          intro A. apply LOADSTORE in A.
          remember (inject_memory j j' BOUND (strip fm) (empmem BOUND) CONSIST SHARED_VALID) as m.
          pose proof (construct_inj_injective j BOUND fl NOREP).
          assert (no_overlap fl (fun b => Plt b BOUND)).
          { unfold valid_block_bset in NOOVERLAP. rewrite strip_valid_block in NOOVERLAP.
            intros b0 n NTH C. eapply NOOVERLAP; eauto.
            eapply dom_match_fm; eauto. }
          specialize (H0 H1 INJECT). rename H0 into INJECTIVE.
          clear LOADBYTES LOADSTORE PERMIFF RANGEPERM FIND FIND' v1 v2 H1.

          generalize 0 A. clear A.
          
          induction initdata; intros. constructor.
          simpl in *. destruct a; destruct A as [A A']; try apply IHinitdata in A'; split; auto.
          exploit load_related; try exact H; eauto. rewrite A. intro. inv H0. inv H3. auto.
          exploit load_related; try exact H; eauto. rewrite A. intro. inv H0. inv H3. auto.
          exploit load_related; try exact H; eauto. rewrite A. intro. inv H0. inv H3. auto.
          exploit load_related; try exact H; eauto. rewrite A. intro. inv H0. inv H3. auto.
          exploit load_related; try exact H; eauto. rewrite A. intro. inv H0. inv H3. auto.
          exploit load_related; try exact H; eauto. rewrite A. intro. inv H0. inv H3. auto.
          unfold Genv.read_as_zero. intros. exploit A; eauto. intro.
          exploit load_related; try exact H; eauto. rewrite H3. intro. inv H4. inv H7; auto.
          destruct chunk; discriminate.
          destruct A as [b1' [FIND1 LOAD1]].
          exploit (ge_match_strict_senv j ge ge_local); auto.
          unfold Senv.find_symbol; simpl. rewrite FIND1. intro. inv H0.
          eexists; split; eauto.
          exploit load_related. eauto. exact H. eauto. rewrite LOAD1. intros. inv H0. inv H5.
          exploit INJECTIVE. exact H6. unfold construct_inj. instantiate (1:= b0).
          destruct plt; auto. exfalso. apply n.
          subst BOUND. erewrite ge_match_strict_next; try exact GEMATCH.
          eapply Genv.genv_symb_range. eauto.
          intro. subst. auto.
        }
        { (* loadbytes *)
          intro A. apply LOADBYTES in A.
          remember (inject_memory j j' BOUND (strip fm) (empmem BOUND) CONSIST SHARED_VALID) as m.
          pose proof (construct_inj_injective j BOUND fl NOREP).
          assert (no_overlap fl (fun b => Plt b BOUND)).
          { unfold valid_block_bset in NOOVERLAP. rewrite strip_valid_block in NOOVERLAP.
            intros b0 n NTH C. eapply NOOVERLAP; eauto.
            eapply dom_match_fm; eauto. }
          specialize (H0 H1 INJECT). rename H0 into INJECTIVE.
          clear LOADBYTES LOADSTORE PERMIFF RANGEPERM FIND FIND' v1 v2 H1.
          exploit loadbytes_related; eauto.
          instantiate (1:= init_data_list_size initdata).
          apply init_data_list_size_pos.
          Transparent Memory.Mem.loadbytes FMemory.Mem.loadbytes.
          unfold Mem.loadbytes in A. instantiate (1:=0). 
          destruct Mem.range_perm_dec; inv A. eapply mem_rel_range_perm; eauto; try constructor.
          rewrite A. intro. inv H0. f_equal.
          generalize x H3 GEMATCH INJECTIVE INJ' INJ. clear. induction initdata; intros.
          inv H3. auto.
         
          simpl in H3. apply list_forall2_split in H3. destruct H3 as (x0 & x1 & EQ & HEAD & TAIL).
          apply IHinitdata in TAIL; auto. clear IHinitdata. subst.
          simpl. f_equal.
          destruct a; simpl in *;
            try match goal with
                | H: context[inj_bytes ?bl] |- _ =>
                  generalize bl x0 H; clear;
                    intros ?l; induction l; inversion 1; subst; auto;
                      match goal with H: memval_related _ _ _ |- _ => inv H; simpl end;
                      f_equal; auto
                end.
          generalize (Z.to_nat z) x0 HEAD INJECTIVE; clear. induction n; intros.
          inv HEAD; auto. inv HEAD. simpl. inv H2. f_equal; auto.

          pose proof (ge_match_strict_senv _ _ _ GEMATCH i).
          unfold Senv.find_symbol in *; simpl in *. inv H; simpl in *.
          rewrite <- H2 in HEAD.
          clear INJ INJ' H2.
          assert (construct_inj j BOUND fl b0 = Some b'0).
          { unfold construct_inj. destruct plt; auto.
            exfalso. apply n. subst BOUND. erewrite ge_match_strict_next; eauto.
            eapply Genv.genv_symb_range; eauto. }
          revert HEAD H INJECTIVE. subst BOUND.
          generalize (construct_inj j (Genv.genv_next ge) fl); clear.
          intros j REL INJ INJECTIVE.
          eapply inj_value_pointer in REL; eauto. 
          rewrite <- H3 in HEAD. revert HEAD.
          generalize (if Archi.ptr64 then 8%nat else 4%nat).
          clear. intros n. revert x0. induction n; intros; inv HEAD; simpl; f_equal; auto.
          inv H2. auto.
        }
      }
    }
          
    { simpl. subst BOUND. inv GEMATCH; auto. }
    { unfold inject_memory at 2. unfold Memory.Mem.valid_block. simpl.
      eapply mem_related_reach_closed; eauto.
      inv INITMEM. subst BOUND. eapply MemClosures.bset_eq_reach_closed; eauto.
    }
  }
Qed.

Lemma init_mem_valid_block:
  forall ge m,
    AsmLang.init_mem ge m ->
    (forall b, Bset.belongsto (valid_block_bset m) b <-> Plt b (Genv.genv_next ge)).
Proof.
  intros. inv H. destruct H0. inv H0.
  destruct x; simpl in *.
  unfold valid_block_bset, strip, Mem.valid_block, GMem.valid_block in *; simpl in *.
  rewrite dom_match_fm. tauto.
Qed.
  

(** construct injection relating symbols, ge_local -> ge *)
Definition bj_constr (ge ge_local: Senv.t) : Bset.inj :=
  fun b => match Senv.invert_symbol ge_local b with
        | Some id => Senv.find_symbol ge b 
        | None => None
        end.



(** regset, loadframe *)
Definition regset_related (j: Bset.inj) (rs_local rs: regset): Prop := forall r, val_related j (rs_local#r) (rs#r).

Definition loadframe_related (j: Bset.inj) (lf_local lf: load_frame) : Prop :=
  match lf_local, lf with
  | mk_load_frame b oty, mk_load_frame b' oty' => j b = Some b' /\ oty = oty'
  end.

Lemma set_regset_related:
  forall j rs rs' r v v',
    regset_related j rs rs' ->
    val_related j v v' ->
    regset_related j (rs # r <- v) (rs' # r <- v').
Proof.
  intros. inv H0; (intro r'; destruct (Pregmap.elt_eq r r');
                   [subst; repeat rewrite Pregmap.gss; constructor; auto | repeat rewrite Pregmap.gso; auto]).
Qed.

Lemma undef_regs_regset_related:
  forall rl j rs rs',
    regset_related j rs rs' ->
    regset_related j (undef_regs rl rs) (undef_regs rl rs').
Proof. induction rl; intros; auto. simpl. apply IHrl. apply set_regset_related; auto. Qed.

Lemma set_res_regset_related:
  forall j br rs rs' v v',
    regset_related j rs rs' ->
    val_related j v v' ->
    regset_related j (set_res br v rs) (set_res br v' rs').
Proof.
  induction br; intros; simpl; auto using set_regset_related.
  apply IHbr2. apply IHbr1. auto. inv H0; simpl; auto. inv H0; simpl; auto.
Qed.
  
Lemma regset_related_val_related:
  forall j rs rs' r, regset_related j rs rs' -> val_related j (rs # r) (rs' # r).
Proof. auto. Qed.

Local Hint Resolve set_regset_related undef_regs_regset_related set_res_regset_related regset_related_val_related.

(** exec_instr related *)
Inductive outcome_related (j: Bset.inj) (bound: block) (fl: freelist) : Asm.outcome -> AsmLang.outcome -> Prop :=
| Stuck_related: outcome_related j bound fl Asm.Stuck AsmLang.Stuck
| Next_related: forall rs rs' m m',
    regset_related (construct_inj j bound fl) rs rs' ->
    mem_related j bound fl (strip m') m ->
    outcome_related j bound fl (Asm.Next rs m) (Next rs' m').

Lemma symbol_address_related:
  forall j (ge ge': genv) id ofs,
    (forall id, option_rel (fun b b' => j b = Some b') (Genv.find_symbol ge id) (Genv.find_symbol ge' id)) ->
    val_related j (Genv.symbol_address ge id ofs) (Genv.symbol_address ge' id ofs).
Proof. intros. specialize (H id). unfold Genv.symbol_address. inv H; try rewrite <- H1, <- H2; constructor; auto. Qed.

Lemma eval_addrmode32_related:
  forall j ge ge' rs rs' a,
    Bset.inj_inject j ->
    (forall id, option_rel (fun b b' => j b = Some b') (Genv.find_symbol ge id) (Genv.find_symbol ge' id)) ->
    regset_related j rs rs' ->
    val_related j (eval_addrmode32 ge a rs) (eval_addrmode32 ge' a rs').
Proof.
  intros. unfold eval_addrmode32.
  destruct a eqn:ADDR; simpl. destruct const; simpl.
  destruct base, ofs as [[ir z']|]; try destruct zeq; auto 20.
  destruct base, ofs as [[ir z']|], p as [id ofs']; try destruct zeq; auto using symbol_address_related.
Qed.

Lemma eval_addrmode64_related:
  forall j ge ge' rs rs' a,
    Bset.inj_inject j ->
    (forall id, option_rel (fun b b' => j b = Some b') (Genv.find_symbol ge id) (Genv.find_symbol ge' id)) ->
    regset_related j rs rs' ->
    val_related j (eval_addrmode64 ge a rs) (eval_addrmode64 ge' a rs').
Proof.
  intros. unfold eval_addrmode64.
  destruct a eqn:ADDR; simpl. destruct const; simpl.
  destruct base, ofs as [[ir z']|]; try destruct zeq; auto 20.
  destruct base, ofs as [[ir z']|], p as [id ofs']; try destruct zeq; auto using symbol_address_related.
Qed.

Lemma eval_addrmode_related:
  forall j ge ge' rs rs' a,
    Bset.inj_inject j ->
    (forall id, option_rel (fun b b' => j b = Some b') (Genv.find_symbol ge id) (Genv.find_symbol ge' id)) ->
    regset_related j rs rs' ->
    val_related j (eval_addrmode ge a rs) (eval_addrmode ge' a rs').
Proof.
  intros. unfold eval_addrmode. destruct Archi.ptr64.
  eapply eval_addrmode64_related; auto. apply eval_addrmode32_related; auto.
Qed.

Lemma exec_load_related:
  forall j ge ge' rs rs' m m' bound fl chunk a rd (NOREP: norep fl),
    Bset.inj_inject (construct_inj j bound fl) ->    
    (forall id, option_rel (fun b b' => (construct_inj j bound fl) b = Some b') (Genv.find_symbol ge id) (Genv.find_symbol ge' id)) ->
    regset_related (construct_inj j bound fl) rs rs' ->
    mem_related j bound fl (strip m') m ->
    outcome_related j bound fl (exec_load ge chunk m a rs rd) (AsmLang.exec_load ge' chunk m' a rs' rd).
Proof.
  intros until rd; intros ? INJECT GENVREL RSREL MEMREL.
  unfold ASM_local.exec_load, AsmLang.exec_load.
  exploit loadv_related; try (intro H; inv H; try rewrite <- H1, <- H2). eauto. eauto. eauto using eval_addrmode_related.
  constructor. rewrite <- H1, <- H0. unfold nextinstr_nf, nextinstr. constructor; auto.
  apply set_regset_related; auto.
  apply offset_ptr_val_related; auto.
Qed.

Lemma exec_store_related:
  forall j ge ge' rs rs' m m' bound fl chunk a r1 destroyed (NOREP: norep fl),
    Bset.inj_inject (construct_inj j bound fl) ->    
    (forall id, option_rel (fun b b' => (construct_inj j bound fl) b = Some b') (Genv.find_symbol ge id) (Genv.find_symbol ge' id)) ->
    regset_related (construct_inj j bound fl) rs rs' ->
    mem_related j bound fl (strip m') m ->
    outcome_related j bound fl (exec_store ge chunk m a rs r1 destroyed) (AsmLang.exec_store ge' chunk m' a rs' r1 destroyed).
Proof.
  intros until destroyed; intros ? INJECT GENVREL RSREL MEMREL.
  unfold ASM_local.exec_store, AsmLang.exec_store.
  exploit storev_related; try (intro H; inv H; try rewrite <- H1, <- H2).
  1-4: eauto using eval_addrmode_related. 
  constructor.
  rewrite <- H0, <- H1. unfold nextinstr_nf, nextinstr; constructor; auto.
  apply set_regset_related; auto.
  apply offset_ptr_val_related; auto.
Qed.

Lemma compare_ints_related:
  forall j bound fl rs rs' m m' x x' y y',
    regset_related (construct_inj j bound fl) rs rs' ->
    mem_related j bound fl (strip m') m ->
    val_related (construct_inj j bound fl) x x' ->
    val_related (construct_inj j bound fl) y y' ->
    Bset.inj_inject (construct_inj j bound fl) ->    
    regset_related (construct_inj j bound fl) (Asm.compare_ints x y rs m) (compare_ints x' y' rs' m').
Proof.
  intros.
  inv H1; inv H2; unfold Asm.compare_ints, compare_ints; simpl; auto;
    repeat (apply set_regset_related; auto);
    unfold Val.cmpu, Val.cmpu_bool; simpl.
  destruct Int.eq; constructor.
  destruct Int.ltu; constructor.
  destruct Archi.ptr64. constructor. destruct Int.eq; simpl; auto.
  repeat erewrite valid_pointer_related; eauto.
  match goal with |- context[if ?x then _ else _] => destruct x end; simpl; constructor.
  destruct Archi.ptr64. constructor. destruct Int.eq; simpl; auto.
  repeat erewrite valid_pointer_related; eauto.
  match goal with |- context[if ?x then _ else _] => destruct x end; simpl; constructor.
  destruct Archi.ptr64. constructor. destruct Int.eq; simpl; auto.
  repeat erewrite valid_pointer_related; eauto.
  match goal with |- context[if ?x then _ else _] => destruct x end; simpl; constructor.
  destruct Archi.ptr64. constructor. destruct Int.eq; simpl; auto.
  repeat erewrite valid_pointer_related; eauto.
  match goal with |- context[if ?x then _ else _] => destruct x end; simpl; constructor.

  destruct Archi.ptr64. constructor.
  repeat erewrite valid_pointer_related; eauto.
  do 2 destruct eq_block; subst; try congruence.
  match goal with |- context[if ?x then _ else _] => destruct x end; simpl; auto.
  destruct Ptrofs.eq; constructor.
  exploit H3. exact H4. exact H1. intro. contradiction.
  match goal with |- context[if ?x then _ else _] => destruct x end; simpl; auto. constructor.

  destruct Archi.ptr64. constructor.
  repeat erewrite valid_pointer_related; eauto.
  do 2 destruct eq_block; subst; try congruence.
  match goal with |- context[if ?x then _ else _] => destruct x end; simpl; auto.
  destruct Ptrofs.ltu; constructor.
  exploit H3. exact H4. exact H1. intro. contradiction.
  match goal with |- context[if ?x then _ else _] => destruct x end; simpl; auto. 

  destruct Archi.ptr64. constructor.
  do 2 destruct eq_block; subst; try congruence; simpl; auto.
  exploit H3. exact H4. exact H1. intro. contradiction.
Qed.

Lemma check_compare_ints_related:
  forall j bound fl m m' x x' y y',
    mem_related j bound fl (strip m') m ->
    val_related (construct_inj j bound fl) x x' ->
    val_related (construct_inj j bound fl) y y' ->
    Bset.inj_inject (construct_inj j bound fl) ->
    Asm.check_compare_ints x y m = check_compare_ints x' y' m'.
Proof.
  intros.
  inv H0; inv H1; unfold Asm.check_compare_ints, check_compare_ints; simpl; auto.
  destruct Archi.ptr64; auto. destruct Int.eq; simpl; auto.
  repeat erewrite valid_pointer_related; eauto.
  destruct Archi.ptr64; auto. destruct Int.eq; simpl; auto.
  repeat erewrite valid_pointer_related; eauto.
  destruct Archi.ptr64; auto.
  repeat erewrite valid_pointer_related; eauto.
  do 2 destruct eq_block; subst; try congruence.
  exploit H2. exact H3. exact H0. intro. contradiction.
Qed.
  
Lemma compare_longs_related:
    forall j bound fl rs rs' m m' x x' y y',
    regset_related (construct_inj j bound fl) rs rs' ->
    mem_related j bound fl (strip m') m ->
    val_related (construct_inj j bound fl) x x' ->
    val_related (construct_inj j bound fl) y y' ->
    regset_related (construct_inj j bound fl) (Asm.compare_longs x y rs m) (compare_longs x' y' rs' m').
Proof.
  intros. inv H0; inv H1; unfold Asm.compare_longs, compare_longs; simpl; auto 10.
  
  repeat apply set_regset_related; auto;
    unfold Val.cmplu, Val.cmplu_bool; inv H2; simpl; auto.
  
  repeat apply set_regset_related; auto;
    unfold Val.cmplu, Val.cmplu_bool; inv H2; simpl; auto.
Qed.

Lemma compare_floats_related:
  forall j rs rs' x x' y y',
    regset_related j rs rs' ->
    val_related j x x' ->
    val_related j y y' ->
    regset_related j (Asm.compare_floats x y rs) (compare_floats x' y' rs').
Proof. intros. inv H0; inv H1; simpl; auto 10. Qed.

Lemma compare_floats32_related:
  forall j rs rs' x x' y y',
    regset_related j rs rs' ->
    val_related j x x' ->
    val_related j y y' ->
    regset_related j (Asm.compare_floats32 x y rs) (compare_floats32 x' y' rs').
Proof. intros. inv H0; inv H1; simpl; auto 10. Qed.

Lemma eval_testcond_related:
  forall j c rs rs',
    regset_related j rs rs' ->
    option_rel eq (eval_testcond c rs) (eval_testcond c rs').
Proof. intros. destruct c; simpl; 
                 repeat match goal with
                        | |- context[rs ?r] => destruct (H r); try constructor; auto
                        end.
Qed.

Local Hint Resolve symbol_address_related eval_addrmode64_related eval_addrmode32_related
      exec_load_related exec_store_related check_compare_ints_related compare_ints_related compare_longs_related
      compare_floats_related compare_floats32_related
      eval_testcond_related.

Lemma range_locset_localize:
  forall j b b' base size,
    j b = Some b' ->
    Bset.inj_inject j ->
    Loclocalize j (range_locset b' base size) (range_locset b base size).
Proof.
  intros. constructor. repeat rewrite range_locset_loc.
  split; intros; Locs.unfolds; rewrite <- H2; unfold range_locset.
  do 2 destruct eq_block; try congruence. subst. exfalso. eauto.
  do 2 destruct eq_block; try congruence. subst. exfalso. eauto.
Qed.

Lemma weak_valid_pointer_fp_localize:
  forall j bound fl m m' b b' ofs,
    norep fl ->
    no_overlap fl (fun b : block => Plt b bound) ->
    Bset.inject j (fun b : block => Plt b bound) (fun b : block => Plt b bound) ->
    mem_related j bound fl (strip m') m ->
    construct_inj j bound fl b = Some b' ->
    FPlocalize (construct_inj j bound fl)
               (weak_valid_pointer_fp m' b' ofs) (MemOpFP.weak_valid_pointer_fp m b ofs).
Proof.
  intros. pose proof (construct_inj_injective _ _ _ H H0 H1).
  unfold weak_valid_pointer_fp, MemOpFP.weak_valid_pointer_fp.
  erewrite valid_pointer_related; eauto.
  destruct (FMemory.Mem.valid_pointer m' b' ofs) eqn:VALID; unfold valid_pointer_fp;
    constructor; simpl; auto using range_locset_localize; try (constructor; tauto).
Qed.

Lemma loadv_fp_localize:
  forall j addr addr' chunk,
    Bset.inj_inject j ->
    val_related j addr addr' ->
    FPlocalize j (FMemOpFP.loadv_fp chunk addr') (FMemOpFP.loadv_fp chunk addr).
Proof.
  intros. inv H0; simpl; auto using FPlocalize_emp.
  unfold FMemOpFP.load_fp. constructor; simpl; constructor; intros; try (tauto; fail).
  repeat rewrite range_locset_loc. split; intros; intuition; subst. eapply H; eauto. congruence.
Qed.

Lemma storev_fp_localize:
  forall j addr addr' chunk,
    Bset.inj_inject j ->
    val_related j addr addr' ->
    FPlocalize j (FMemOpFP.storev_fp chunk addr') (FMemOpFP.storev_fp chunk addr).
Proof.
  intros. inv H0; simpl; auto using FPlocalize_emp.
  unfold FMemOpFP.store_fp. constructor; simpl; constructor; intros; try (tauto; fail).
  repeat rewrite range_locset_loc. split; intros; intuition; subst. eapply H; eauto. congruence.
Qed.

Lemma cmpu_fp_localize:
  forall j bound fl m m' v1 v1' v2 v2' c,
    norep fl ->
    no_overlap fl (fun b0 : block => Plt b0 bound) ->
    Bset.inject j (fun b0 : block => Plt b0 bound) (fun b0 : block => Plt b0 bound) ->
    mem_related j bound fl (strip m') m ->
    val_related (construct_inj j bound fl) v1 v1' ->
    val_related (construct_inj j bound fl) v2 v2' ->
    FPlocalize (construct_inj j bound fl)
               (of_optfp (Cop_fp.cmpu_bool_fp m' c v1' v2'))
               (ValFP.cmpu_bool_fp_total m c v1 v2).
Proof.
  intros. inv H3; inv H4;
            unfold ValFP.cmpu_bool_fp_total, Cop_fp.cmpu_bool_fp_total; simpl; auto using FPlocalize_emp;
              destruct Archi.ptr64; auto using FPlocalize_emp;
                repeat match goal with
                       | |- context[match ?x with _ => _ end] =>
                         destruct x; simpl; auto
                       end;
                repeat apply FPlocalize_union; auto using FPlocalize_emp, weak_valid_pointer_fp_localize, FPlocalize_cmp_undef;
                  try congruence.
  subst. exfalso. apply n. eapply construct_inj_injective; eauto.
  subst. exfalso. apply n. eapply construct_inj_injective; eauto.
  subst. exfalso. apply n. eapply construct_inj_injective; eauto.
  unfold valid_pointer_fp. constructor; simpl; auto using range_locset_localize, construct_inj_injective; constructor; tauto.
  unfold valid_pointer_fp. constructor; simpl; auto using range_locset_localize, construct_inj_injective; constructor; tauto.
Qed.

Lemma exec_load_fp_localize:
  forall j ge ge' rs rs' bound fl chunk a ,
    norep fl ->
    no_overlap fl (fun b : block => Plt b bound) ->
    Bset.inject j (fun b : block => Plt b bound) (fun b : block => Plt b bound) ->
    (forall id, option_rel (fun b b' => (construct_inj j bound fl) b = Some b') (Genv.find_symbol ge id) (Genv.find_symbol ge' id)) ->
    regset_related (construct_inj j bound fl) rs rs' ->
    FPlocalize (construct_inj j bound fl) (AsmLang.exec_load_fp ge' chunk a rs') (exec_load_fp ge chunk a rs).
Proof.
  intros until a; intros NOREP NOOVERLAP INJECT GENVREL RSREL.
  unfold exec_load_fp, AsmLang.exec_load_fp; simpl.
  pose proof (construct_inj_injective _ _ _ NOREP NOOVERLAP INJECT).
  apply loadv_fp_localize; auto.
Qed.

Lemma exec_store_fp_localize:
  forall j ge ge' rs rs' bound fl chunk a ,
    norep fl ->
    no_overlap fl (fun b : block => Plt b bound) ->
    Bset.inject j (fun b : block => Plt b bound) (fun b : block => Plt b bound) ->
    (forall id, option_rel (fun b b' => (construct_inj j bound fl) b = Some b') (Genv.find_symbol ge id) (Genv.find_symbol ge' id)) ->
    regset_related (construct_inj j bound fl) rs rs' ->
    FPlocalize (construct_inj j bound fl) (AsmLang.exec_store_fp ge' chunk a rs') (exec_store_fp ge chunk a rs).
Proof.
  intros until a; intros NOREP NOOVERLAP INJECT GENVREL RSREL.
  unfold exec_store_fp, AsmLang.exec_store_fp; simpl.
  pose proof (construct_inj_injective _ _ _ NOREP NOOVERLAP INJECT).
  apply storev_fp_localize; auto.
Qed.

(** TODO: Move to ? *)
Lemma locs_union_same:
  forall ls, Locs.union ls ls = ls.
Proof. intros. unfold Locs.union. do 2 (apply Axioms.functional_extensionality; intro; simpl). apply orb_diag. Qed.
Lemma fp_union_same:
  forall fp, FP.union fp fp = fp.
Proof. destruct fp. unfold FP.union. f_equal; simpl; apply locs_union_same. Qed.
  
Lemma compare_ints_fp_localize:
  forall j bound fl m m' x x' y y',
    norep fl ->
    no_overlap fl (fun b : block => Plt b bound) ->
    Bset.inject j (fun b : block => Plt b bound) (fun b : block => Plt b bound) ->
    mem_related j bound fl (strip m') m ->
    val_related (construct_inj j bound fl) x x' ->
    val_related (construct_inj j bound fl) y y' ->
    FPlocalize (construct_inj j bound fl) (AsmLang.compare_ints_fp x' y' m') (ASM_local.compare_ints_fp x y m).
Proof.
  intros. pose proof (construct_inj_injective _ _ _ H H0 H1).
  inv H4; inv H3; unfold ASM_local.compare_ints_fp, AsmLang.compare_ints_fp;
    simpl; repeat match goal with |- context[match ?x with _ => _ end] => destruct x end;
      repeat rewrite FP.fp_union_emp; repeat rewrite fp_union_same; try apply FPlocalize_emp;
        simpl; subst; try congruence; repeat apply FPlocalize_union;
          auto using weak_valid_pointer_fp_localize, FPlocalize_cmp_undef.
  exfalso. eauto.
  exfalso. eauto.
  unfold valid_pointer_fp; constructor; simpl; auto using range_locset_localize; constructor; tauto.
  unfold valid_pointer_fp; constructor; simpl; auto using range_locset_localize; constructor; tauto.
Qed.

Lemma compare_longs_fp_localize:
  forall j bound fl m m' x x' y y',
    norep fl ->
    no_overlap fl (fun b : block => Plt b bound) ->
    Bset.inject j (fun b : block => Plt b bound) (fun b : block => Plt b bound) ->
    mem_related j bound fl (strip m') m ->
    val_related (construct_inj j bound fl) x x' ->
    val_related (construct_inj j bound fl) y y' ->
    FPlocalize (construct_inj j bound fl) (AsmLang.compare_longs_fp x' y' m') (ASM_local.compare_longs_fp x y m).
Proof.
  intros. pose proof (construct_inj_injective _ _ _ H H0 H1).
  inv H4; inv H3;
    simpl;
    repeat match goal with |- context[match ?x with _ => _ end] => destruct x eqn:?Hx end;
      repeat rewrite FP.fp_union_emp; repeat rewrite fp_union_same; try apply FPlocalize_emp;
        simpl; subst; try congruence; repeat apply FPlocalize_union;
          simpl; auto using weak_valid_pointer_fp_localize, FPlocalize_cmp_undef.
Qed.

(** fpG *)
Lemma construct_inj_block_G:
  forall j bound fl b b',
    Bset.inject j (fun b => Plt b bound) (fun b => Plt b bound) ->
    construct_inj j bound fl b = Some b' ->
    Bset.belongsto (fun b => Plt b bound) b' \/ (exists n, get_block fl n = b').
Proof.
  unfold construct_inj. intros. destruct plt.
  left. eapply Bset.inj_range' in H0; inv H; eauto.
  right. inv H0. eauto.
Qed.

Ltac red_blocks0 :=
  repeat match goal with
           | |- context[match ?x with _ => _ end] => destruct x; subst
           | |- context[FP.union _ _] => apply fpG_union
         end.
Ltac red_blocks :=
  red_blocks0;
    simpl; try apply fpG_emp; intros ?b BLOCKS;
      unfold Bset.belongsto, FP.blocks, FP.locs, store_fp, Locs.blocks in *; simpl in *;
        repeat rewrite Locs.locs_union_emp in BLOCKS; repeat rewrite Locs.emp_union_locs in BLOCKS;
          destruct BLOCKS as (? & BLOCKS); apply range_locset_loc in BLOCKS; destruct BLOCKS as [BLOCKS _]; subst;
            eapply construct_inj_block_G; eauto.

Lemma exec_load_fp_fpG:
  forall j fl bound (ge ge': genv) rs rs' chunk a,
    norep fl ->
    no_overlap fl (fun b : block => Plt b bound) ->
    (Bset.inject j (fun b => Plt b bound) (fun b => Plt b bound)) ->
    (forall id, option_rel (fun b b' => (construct_inj j bound fl) b = Some b') (Genv.find_symbol ge id) (Genv.find_symbol ge' id)) ->
    regset_related (construct_inj j bound fl) rs rs' ->
    fpG fl (fun b => Plt b bound) (AsmLang.exec_load_fp ge' chunk a rs').
Proof.
  intros until a. intros NOREP NOOVERLAP INJECT GENVREL RSREL.
  pose proof (construct_inj_injective _ _ _ NOREP NOOVERLAP INJECT) as INJECTIVE.
  unfold AsmLang.exec_load_fp. exploit eval_addrmode_related; eauto. instantiate (1:= a).
  intro A. destruct A; red_blocks.
Qed.

Lemma exec_store_fp_fpG:
  forall j fl bound (ge ge': genv) rs rs' chunk a,
    norep fl ->
    no_overlap fl (fun b : block => Plt b bound) ->
    (Bset.inject j (fun b => Plt b bound) (fun b => Plt b bound)) ->
    (forall id, option_rel (fun b b' => (construct_inj j bound fl) b = Some b') (Genv.find_symbol ge id) (Genv.find_symbol ge' id)) ->
    regset_related (construct_inj j bound fl) rs rs' ->
    fpG fl (fun b => Plt b bound) (AsmLang.exec_store_fp ge' chunk a rs').
Proof.
  intros until a. intros NOREP NOOVERLAP INJECT GENVREL RSREL.
  pose proof (construct_inj_injective _ _ _ NOREP NOOVERLAP INJECT) as INJECTIVE.
  unfold AsmLang.exec_store_fp. exploit eval_addrmode_related; eauto. instantiate (1:= a).
  intro A. destruct A; red_blocks.
Qed.

Lemma compare_ints_fp_fpG:
  forall j fl bound m m' v1 v2 v1' v2',
    norep fl ->
    no_overlap fl (fun b : block => Plt b bound) ->
    (Bset.inject j (fun b => Plt b bound) (fun b => Plt b bound)) ->
    mem_related j bound fl (strip m') m ->
    val_related (construct_inj j bound fl) v1 v1' ->
    val_related (construct_inj j bound fl) v2 v2' ->
    fpG fl (fun b => Plt b bound) (AsmLang.compare_ints_fp v1' v2' m').
Proof.
  intros until v2'. intros NOREP NOOVERLAP INJECT MEMREL VREL1 VREL2.
  pose proof (construct_inj_injective _ _ _ NOREP NOOVERLAP INJECT).
  unfold AsmLang.compare_ints_fp.
  inv VREL1; inv VREL2; simpl; unfold weak_valid_pointer_fp, valid_pointer_fp; simpl; try red_blocks.
  
Qed.

Lemma compare_longs_fp_fpG:
   forall j fl bound m m' v1 v2 v1' v2',
    norep fl ->
    no_overlap fl (fun b : block => Plt b bound) ->
    (Bset.inject j (fun b => Plt b bound) (fun b => Plt b bound)) ->
    mem_related j bound fl (strip m') m ->
    val_related (construct_inj j bound fl) v1 v1' ->
    val_related (construct_inj j bound fl) v2 v2' ->
    fpG fl (fun b => Plt b bound) (AsmLang.compare_longs_fp v1' v2' m').
Proof.
  intros until v2'. intros NOREP NOOVERLAP INJECT MEMREL VREL1 VREL2.
  pose proof (construct_inj_injective _ _ _ NOREP NOOVERLAP INJECT).
  unfold AsmLang.compare_longs_fp.
  inv VREL1; inv VREL2; simpl; unfold weak_valid_pointer_fp, valid_pointer_fp; simpl; red_blocks.
Qed.

Ltac solv_rel :=
  match goal with
  | H: regset_related ?j ?rs ?rs' |- context[eval_testcond ?c ?rs] =>
    destruct (eval_testcond_related j c rs rs' H); solv_rel
  | H: regset_related _ ?rs _ |- context[match ?rs ?r with _ => _ end] => destruct (H r); solv_rel
  | |- context[match ?x with _ => _ end] => destruct x; solv_rel
  | |- outcome_related _ _ _ (exec_load _ _ _ _ _ _) _ =>
    eapply exec_load_related; eauto; solv_rel
  | |- outcome_related _ _ _ (exec_store _ _ _ _ _ _ _) _ =>
    eapply exec_store_related; eauto; solv_rel
  | |- outcome_related _ _ _ _ _ =>
    constructor; auto; unfold nextinstr_nf, nextinstr; solv_rel
  | |- regset_related _ (_ # _ <- _) (_ # _ <- _) =>
    apply set_regset_related; auto; solv_rel
  | |- regset_related _ (undef_regs _ _) (undef_regs _ _) =>
    apply undef_regs_regset_related; eauto; solv_rel
  | |- val_related _ (Val.offset_ptr _ _) (Val.offset_ptr _ _) =>
    apply offset_ptr_val_related; eauto; solv_rel
  | |- val_related _ (eval_addrmode32 _ _ _) (eval_addrmode32 _ _ _) =>
    apply eval_addrmode_related; eauto; solv_rel
  | |- val_related _ (_ # _) (_ # _) =>
    apply regset_related_val_related; auto; solv_rel
  | |- val_related _ (Val.zero_ext _ _) _ =>
    apply zero_ext_related; eauto; solv_rel
  | |- val_related _ (Val.sign_ext _ _) _ =>
    apply sign_ext_related; eauto; solv_rel
  | |- val_related _ (Val.maketotal _) _ =>
    apply maketotal_related; eauto; solv_rel
  | b: bool |- _ => destruct b; solv_rel
  | _ => subst; try (constructor; fail); try (congruence; fail)
  end; subst.

Lemma val_related_check_undef:
  forall j x1 x2 y1 y2,
    val_related j x1 y1 ->
    val_related j x2 y2 ->
    check_vundef x1 x2 = check_vundef y1 y2.
Proof. intros. inv H0; inv H; auto. Qed.

Lemma exec_instr_related:
  forall j ge ge' f i rs rs' m m' fl bound,
    fl = FMemory.Mem.freelist m' ->
    norep fl ->
    no_overlap fl (fun b : block => Plt b bound) ->
    (Bset.inject j (fun b => Plt b bound) (fun b => Plt b bound)) ->
    (forall id, option_rel (fun b b' => (construct_inj j bound fl) b = Some b') (Genv.find_symbol ge id) (Genv.find_symbol ge' id)) ->
    regset_related (construct_inj j bound fl) rs rs' ->
    mem_related j bound fl (strip m') m ->
    outcome_related j bound fl (ASM_local.exec_instr ge f i rs m) (AsmLang.exec_instr ge' f i rs' m') /\
    FPlocalize (construct_inj j bound fl) (AsmLang.exec_instr_fp ge' f i rs' m') (ASM_local.exec_instr_fp ge f i rs m) /\
    fpG fl (fun b => Plt b bound) (AsmLang.exec_instr_fp ge' f i rs' m').
Proof.
  intros until bound. intros FL NOREP NOOVERLAP INJECT GENVREL RSREL MEMREL.
  pose proof (construct_inj_injective _ _ _ NOREP NOOVERLAP INJECT) as INJECTIVE.
  destruct i; (split; [ try (simpl; unfold Vzero, goto_label, AsmLang.goto_label; solv_rel; fail)
                      | simpl; unfold Vzero; split;
                        [ auto 10 using FPlocalize_emp, exec_load_fp_localize, exec_store_fp_localize,
                          compare_ints_fp_localize, compare_longs_fp_localize
                        | eauto using fpG_emp, exec_load_fp_fpG, exec_store_fp_fpG,
                          compare_ints_fp_fpG, compare_longs_fp_fpG]]).
  1-8 : unfold AsmLang.exec_instr, exec_instr; simpl.
  1-8 : match goal with
        | |- outcome_related ?j ?bound ?fl (match check_vundef ?x1 ?x2 with _ => _ end)
                            (match check_vundef ?y1 ?y2 with _ => _ end)
          => assert (val_related (construct_inj j bound fl) x1 y1) as ?H1 by solv_rel;
              assert (val_related (construct_inj j bound fl) x2 y2) as ?H2 by solv_rel;
              pose proof (val_related_check_undef _ _ _ _ _ H1 H2) as ?HC;
              pose proof (check_compare_ints_related _ _ _ _ _ _ _ _ _ MEMREL H1 H2 INJECTIVE) as ?HC';
              rewrite HC; clear HC; try rewrite HC'; clear HC';
                destruct check_vundef; try destruct check_compare_ints; try solv_rel; auto 10;
                  try (inv H1; inv H2; simpl; unfold Vzero; auto 10)
        end.
  { simpl; unfold goto_label, AsmLang.goto_label.
    destruct (RSREL r); try constructor.
    assert (val_related (construct_inj j bound fl)
                        ((rs # RAX <- Vundef) # RDX <- Vundef PC)
                        ((rs' # RAX <- Vundef) # RDX <- Vundef PC)) by auto.
    destruct H; solv_rel. }
  (** alloc *)
  { simpl. destruct (Memory.Mem.alloc m 0 sz) as [m1 stk] eqn:ALLOC.
    destruct (FMemory.Mem.alloc m' 0 sz) as [m1' stk'] eqn:ALLOC'.
    exploit alloc_related; eauto. intro MEMREL1.
    exploit alloc_result_related; eauto. intro STKREL.
    exploit storev_related.
    eauto. exact MEMREL1. eapply rel_ptr. exact STKREL. apply (RSREL RSP). intro MEMREL2. inv MEMREL2.
    rewrite <- H, <- H0. constructor. rewrite <- H, <- H0.
    exploit storev_related.
    eauto. exact H1. eapply rel_ptr. exact STKREL. apply (RSREL RA). intro MEMREL3. inv MEMREL3.
    rewrite <- H3, <- H4. constructor. rewrite <- H3, <- H2. solv_rel. }
  (** alloc fp *)
  { destruct (Memory.Mem.alloc _ _ _) as [m1 stk] eqn:ALLOC.
    destruct (FMemory.Mem.alloc _ _ _) as [m1' stk'] eqn:ALLOC'.
    exploit alloc_result_related; eauto. intro STKREL.
    repeat apply FPlocalize_union.
    2: fold (storev_fp Mptr (Vptr stk (Ptrofs.add Ptrofs.zero ofs_link)))
            (storev_fp Mptr (Vptr stk' (Ptrofs.add Ptrofs.zero ofs_link))).
    3: fold (storev_fp Mptr (Vptr stk (Ptrofs.add Ptrofs.zero ofs_ra)))
            (storev_fp Mptr (Vptr stk' (Ptrofs.add Ptrofs.zero ofs_ra))).
    all: auto using storev_fp_localize.
    unfold alloc_fp, MemOpFP.alloc_fp, uncheck_alloc_fp.
    erewrite <- Memory.Mem.alloc_result, <- FMemory.Mem.alloc_result; eauto.
    constructor; simpl; try (constructor; tauto); auto using range_locset_localize.
    constructor; intros. Locs.unfolds. do 2 destruct peq; try tauto.
    subst. exploit construct_inj_injective. eauto. eauto. eauto. exact H. exact STKREL.
    congruence.
    subst. congruence.
  }
  (** alloc fpG *)
  { unfold store_fp; simpl.
    destruct (Memory.Mem.alloc m 0 sz) as [m1 stk] eqn:ALLOC.
    destruct (FMemory.Mem.alloc _ _ _) as [m1' stk'] eqn:ALLOC'.
    exploit alloc_result_related; eauto. intro STKREL.
    red_blocks0; try red_blocks. unfold fpG. intros b BLOCKS.
    right. eapply FMemory.Mem.alloc_result in ALLOC'; eauto.
    subst. unfold Bset.belongsto,FP.blocks,Locs.blocks in BLOCKS.
    destruct BLOCKS. eapply alloc_fp_loc in H; eauto.
  }
  (** free *)
  { simpl. exploit loadv_related. eauto. exact MEMREL. apply offset_ptr_val_related. apply (RSREL RSP).
    intro A. inv A; rewrite <- H, <- H0. constructor.
    exploit loadv_related. eauto. exact MEMREL. apply offset_ptr_val_related. apply (RSREL RSP).
    intro A. inv A. rewrite <- H3, <- H4. constructor.
    rewrite <- H2, <- H3. destruct (RSREL RSP); try constructor.
    exploit free_related; eauto. intro A. inv A.
    rewrite <- H7, <- H8. constructor. rewrite <- H6, <- H7. solv_rel. }
  (** free fp *)
  { destruct (RSREL RSP); try apply FPlocalize_emp.
    repeat apply FPlocalize_union.
    1-2: apply loadv_fp_localize; solv_rel; auto.
    unfold free_fp. constructor; try (constructor; tauto). simpl. apply range_locset_localize; auto. }
  (** free fpG *)
  { destruct (RSREL RSP); red_blocks. }
Qed.

Lemma exec_instr_fl_unchanged:
  forall ge fn i rs m rs' m',
    AsmLang.exec_instr ge fn i rs m = Next rs' m' ->
    FMemory.Mem.freelist m' = FMemory.Mem.freelist m.
Proof.
  intros.
  destruct i; unfold AsmLang.exec_load, AsmLang.exec_store, AsmLang.goto_label in *;
    simpl in *; inv H; auto;
    repeat match goal with
           | H: context[AsmLang.exec_load]|- _ =>
             unfold AsmLang.exec_load in H; destruct FMemory.Mem.loadv; inv H; auto
           | H: context[AsmLang.exec_store]|- _ =>
             unfold AsmLang.exec_store in H; destruct eval_addrmode; simpl in H; try discriminate;
               destruct FMemory.Mem.store eqn:?; inv H; eapply FMemory.Mem.store_freelist; eauto
           | H: context[AsmLang.goto_label]|- _ => unfold AsmLang.goto_label in H
           | H: context[match ?x with _ => _ end] |- _ => destruct x eqn:?; try discriminate
           | H: Next _ _ = Next _ _ |- _ => inv H; auto
           end.
  erewrite FMemory.Mem.store_freelist; try eassumption.
  erewrite FMemory.Mem.store_freelist; try eassumption.
  erewrite FMemory.Mem.alloc_freelist; try eassumption. auto.
  erewrite FMemory.Mem.free_freelist; try eassumption. auto.
Qed.

(** builtin args *)
Lemma eval_builtin_arg_related:
  forall j bound fl arg ge ge' rs rs' vsp vsp' m m' varg,
    norep fl ->
    no_overlap fl (fun b : block => Plt b bound) ->
    (Bset.inject j (fun b => Plt b bound) (fun b => Plt b bound)) ->
    (forall id, option_rel (fun b b' => (construct_inj j bound fl) b = Some b') (Senv.find_symbol ge id) (Senv.find_symbol ge' id)) ->
    regset_related (construct_inj j bound fl) rs rs' ->
    val_related (construct_inj j bound fl) vsp vsp' ->
    mem_related j bound fl (strip m') m ->
    Events.eval_builtin_arg ge rs vsp m arg varg ->
    exists varg', AsmLang.eval_builtin_arg ge' rs' vsp' m' arg varg' /\
             val_related (construct_inj j bound fl) varg varg'.
Proof.
  intros until varg. intros NOREP NOOVERLAP INJECT GEREL RSREL SPREL MEMREL EVAL.
  pose proof (construct_inj_injective _ _ _ NOREP NOOVERLAP INJECT) as INJECTIVE.
  revert varg EVAL.
  induction arg; intros; inv EVAL; simpl in *; try (eexists; split; [econstructor; eauto|eauto]; fail).
  exploit loadv_related. eauto. eauto. apply offset_ptr_val_related. eauto. intro H. inv H.
  rewrite H2 in H1. discriminate.
  eexists; split; [econstructor; eauto| eauto]. rewrite H2 in H0. inv H0. auto.
  eexists; split. econstructor; eauto. apply offset_ptr_val_related. auto.
  specialize (GEREL id). unfold Senv.symbol_address in H3; simpl in *. inv GEREL.
  rewrite <- H0 in H3. discriminate. rewrite <- H in H3.
  exploit loadv_related. eauto. eauto. apply rel_ptr. eauto. instantiate (1:=ofs). intro REL. inv REL.
  simpl in H3. rewrite H3 in H4. discriminate.
  eexists; split; [econstructor | eauto]. unfold Senv.symbol_address. rewrite <- H0. eauto.
  simpl in H3. rewrite H3 in H2. inv H2. auto.
  eexists. split. econstructor. unfold Senv.symbol_address. specialize (GEREL id). inv GEREL; auto.
  exploit IHarg1. eauto. exploit IHarg2. eauto. intros [vlo' [EVAL2 REL2]] [vhi' [EVAL1 REL1]].
  eexists. split. econstructor; eauto. apply longofwors_related; auto.
Qed.

Lemma eval_builtin_arg_related':
  forall j bound fl arg ge ge' rs rs' vsp vsp' m m' varg',
    norep fl ->
    no_overlap fl (fun b : block => Plt b bound) ->
    (Bset.inject j (fun b => Plt b bound) (fun b => Plt b bound)) ->
    (forall id, option_rel (fun b b' => (construct_inj j bound fl) b = Some b') (Senv.find_symbol ge id) (Senv.find_symbol ge' id)) ->
    regset_related (construct_inj j bound fl) rs rs' ->
    val_related (construct_inj j bound fl) vsp vsp' ->
    mem_related j bound fl (strip m') m ->
    AsmLang.eval_builtin_arg ge' rs' vsp' m' arg varg' ->
    exists varg, Events.eval_builtin_arg ge rs vsp m arg varg /\
             val_related (construct_inj j bound fl) varg varg'.
Proof.
  intros until varg'. intros NOREP NOOVERLAP INJECT GEREL RSREL SPREL MEMREL EVAL.
  pose proof (construct_inj_injective _ _ _ NOREP NOOVERLAP INJECT) as INJECTIVE.
  revert varg' EVAL.
  induction arg; intros; inv EVAL; simpl in *; try (eexists; split; [econstructor; eauto|eauto]; fail).
  exploit loadv_related. eauto. eauto. apply offset_ptr_val_related. eauto. intro H. inv H.
  rewrite H2 in H3. discriminate.
  eexists; split; [econstructor; eauto| eauto]. rewrite H2 in H1. inv H1. auto.
  eexists; split. econstructor; eauto. apply offset_ptr_val_related. auto.
  specialize (GEREL id). unfold Senv.symbol_address in H3; simpl in *. inv GEREL.
  rewrite <- H in H3. discriminate. rewrite <- H0 in H3.
  exploit loadv_related. eauto. eauto. apply rel_ptr. eauto. instantiate (1:=ofs). intro REL. inv REL.
  simpl in H3. rewrite H3 in H5. discriminate.
  eexists; split; [econstructor | eauto]. unfold Senv.symbol_address. rewrite <- H. eauto.
  simpl in H3. rewrite H3 in H4. inv H4. auto.
  eexists. split. econstructor. unfold Senv.symbol_address. specialize (GEREL id). inv GEREL; auto.
  exploit IHarg1. eauto. exploit IHarg2. eauto. intros [vlo' [EVAL2 REL2]] [vhi' [EVAL1 REL1]].
  eexists. split. econstructor; eauto. apply longofwors_related; auto.
Qed.

Lemma eval_builtin_arg_fp_localize':
  forall j arg ge ge' rs rs' vsp vsp' fp',
    Bset.inj_inject j ->
    (forall id, option_rel (fun b b' => j b = Some b') (Senv.find_symbol ge id) (Senv.find_symbol ge' id)) ->
    regset_related j rs rs' ->
    val_related j vsp vsp' ->
    MemOpFP.eval_builtin_arg_fp ge' rs' vsp' arg fp' ->
    exists fp, MemOpFP.eval_builtin_arg_fp ge rs vsp arg fp /\
          FPlocalize j fp' fp.
Proof.
  induction arg; intros; inv H3; try (eexists; split; [econstructor; eauto|apply FPlocalize_emp]; fail).
  eexists. split. econstructor. apply loadv_fp_localize; auto. apply offset_ptr_val_related. auto.
  eexists. split. econstructor. apply loadv_fp_localize; auto.
  unfold Senv.symbol_address. destruct (H0 id); auto.
  exploit IHarg1; eauto. exploit IHarg2; eauto. intros [fp2' [EVAL2 REL2]] [fp1' [EVAL1 REL1]].
  eexists. split. econstructor; eauto. apply FPlocalize_union; auto.
Qed.

Lemma eval_builtin_arg_fp_localize:
  forall j bound fl ge ge' rs rs' vsp vsp' arg fp,
    norep fl ->
    no_overlap fl (fun b : block => Plt b bound) ->
    (Bset.inject j (fun b => Plt b bound) (fun b => Plt b bound)) ->
    (forall id, option_rel (fun b b' => (construct_inj j bound fl) b = Some b') (Senv.find_symbol ge id) (Senv.find_symbol ge' id)) ->
    regset_related (construct_inj j bound fl) rs rs' ->
    val_related (construct_inj j bound fl) vsp vsp' ->
    MemOpFP.eval_builtin_arg_fp ge rs vsp arg fp ->
    exists fp', MemOpFP.eval_builtin_arg_fp ge' rs' vsp' arg fp' /\
           FPlocalize (construct_inj j bound fl) fp' fp /\ fpG fl (fun b => Plt b bound) fp'.
Proof.
  intros until fp. intros NOREP NOOVERLAP INJECT GEREL RSREL SPREL.
  pose proof (construct_inj_injective _ _ _ NOREP NOOVERLAP INJECT) as INJECTIVE.
  revert fp.
  induction arg; intros; inv H; try (eexists; split; [econstructor; eauto|split;[apply FPlocalize_emp|apply fpG_emp]]; fail).
  eexists. split. econstructor. split. apply loadv_fp_localize; auto. apply offset_ptr_val_related. auto.
  unfold loadv_fp, load_fp; inv SPREL; simpl; red_blocks.
  eexists. split. econstructor. split. apply loadv_fp_localize; auto.
  unfold Senv.symbol_address. destruct (GEREL id); auto.
  unfold loadv_fp, load_fp, Senv.symbol_address; destruct (GEREL id); simpl; red_blocks.
  exploit IHarg1; eauto. exploit IHarg2; eauto. intros [fp2' [EVAL2 [REL2 FPG2]]] [fp1' [EVAL1 [REL1 FPG1]]].
  eexists. split. econstructor; eauto. split. apply FPlocalize_union; auto. apply fpG_union; auto.
Qed.

Lemma eval_builtin_args_related:
  forall j bound fl args ge ge' rs rs' vsp vsp' m m' vargs,
    norep fl ->
    no_overlap fl (fun b : block => Plt b bound) ->
    (Bset.inject j (fun b => Plt b bound) (fun b => Plt b bound)) ->
    (forall id, option_rel (fun b b' => (construct_inj j bound fl) b = Some b') (Senv.find_symbol ge id) (Senv.find_symbol ge' id)) ->
    regset_related (construct_inj j bound fl) rs rs' ->
    val_related (construct_inj j bound fl) vsp vsp' ->
    mem_related j bound fl (strip m') m ->
    Events.eval_builtin_args ge rs vsp m args vargs ->
    exists vargs', AsmLang.eval_builtin_args ge' rs' vsp' m' args vargs' /\
              list_forall2 (val_related (construct_inj j bound fl)) vargs vargs'.
Proof.
  induction args; intros. exists nil. inv H6. split; econstructor.
  inv H6. exploit IHargs; eauto. intros [vargs' [EVALs RELs]].
  exploit eval_builtin_arg_related; eauto. intros [varg' [EVAL REL]].
  eexists. split; econstructor; eauto.
Qed.

Lemma eval_builtin_args_related':
  forall j bound fl args ge ge' rs rs' vsp vsp' m m' vargs',
    norep fl ->
    no_overlap fl (fun b : block => Plt b bound) ->
    (Bset.inject j (fun b => Plt b bound) (fun b => Plt b bound)) ->
    (forall id, option_rel (fun b b' => (construct_inj j bound fl) b = Some b') (Senv.find_symbol ge id) (Senv.find_symbol ge' id)) ->
    regset_related (construct_inj j bound fl) rs rs' ->
    val_related (construct_inj j bound fl) vsp vsp' ->
    mem_related j bound fl (strip m') m ->
    AsmLang.eval_builtin_args ge' rs' vsp' m' args vargs' ->
    exists vargs, Events.eval_builtin_args ge rs vsp m args vargs /\
             list_forall2 (val_related (construct_inj j bound fl)) vargs vargs'.
Proof.
  induction args; intros. exists nil. inv H6. split; econstructor.
  inv H6. exploit IHargs; eauto. intros [vargs [EVALs RELs]].
  exploit eval_builtin_arg_related'; eauto. intros [varg [EVAL REL]].
  eexists. split; econstructor; eauto.
Qed.

Lemma eval_builtin_args_fp_localize':
  forall j args ge ge' rs rs' vsp vsp' fp',
    Bset.inj_inject j ->
    (forall id, option_rel (fun b b' => j b = Some b') (Senv.find_symbol ge id) (Senv.find_symbol ge' id)) ->
    regset_related j rs rs' ->
    val_related j vsp vsp' ->
    MemOpFP.eval_builtin_args_fp ge' rs' vsp' args fp' ->
    exists fp, MemOpFP.eval_builtin_args_fp ge rs vsp args fp /\
          FPlocalize j fp' fp.
Proof.
  induction args; intros. inv H3. eexists. split. econstructor. apply FPlocalize_emp.
  inv H3. exploit IHargs; eauto. intros [fp2' [EVALFP2 RELFP2]].
  exploit eval_builtin_arg_fp_localize'; eauto. intros [fp1' [EVALFP1 RELFP1]].
  eexists. split. econstructor; eauto. apply FPlocalize_union; auto.
Qed.

Lemma eval_builtin_args_fp_localize:
  forall j bound fl ge ge' rs rs' vsp vsp' args fp,
    norep fl ->
    no_overlap fl (fun b : block => Plt b bound) ->
    (Bset.inject j (fun b => Plt b bound) (fun b => Plt b bound)) ->
    (forall id, option_rel (fun b b' => (construct_inj j bound fl) b = Some b') (Senv.find_symbol ge id) (Senv.find_symbol ge' id)) ->
    regset_related (construct_inj j bound fl) rs rs' ->
    val_related (construct_inj j bound fl) vsp vsp' ->
    MemOpFP.eval_builtin_args_fp ge rs vsp args fp ->
    exists fp', MemOpFP.eval_builtin_args_fp ge' rs' vsp' args fp' /\
           FPlocalize (construct_inj j bound fl) fp' fp /\ fpG fl (fun b => Plt b bound) fp'.
Proof.
  induction args; intros. inv H5. eexists. split. econstructor. split; auto using FPlocalize_emp, fpG_emp.
  inv H5. exploit eval_builtin_arg_fp_localize; eauto. exploit IHargs; eauto.
  intros [fp2' [EVAL2 [FPREL2 FPG2]]] [fp1' [EVAL1 [FPREL1 FPG1]]].
  eexists. split. econstructor; eauto. split; auto using FPlocalize_union, fpG_union.
Qed.

(** ext arguments *)
Lemma extcall_arg_related:
  forall j bound fl rs rs' m m' l varg (NOREP: norep fl),
    regset_related (construct_inj j bound fl) rs rs' ->
    mem_related j bound fl (strip m') m ->
    Asm.extcall_arg rs m l varg ->
    exists varg', AsmLang.extcall_arg rs' m' l varg' /\ val_related (construct_inj j bound fl) varg varg'.
Proof.
  intros. inv H1. eexists. split. constructor. auto.
  exploit loadv_related. eauto. eauto. apply offset_ptr_val_related. exact (H RSP).
  intro A. inv A. rewrite H3 in H2. discriminate.
  eexists. split. econstructor; eauto. rewrite H3 in H1. inv H1. auto.
Qed.

Lemma extcall_arg_related':
  forall j bound fl rs rs' m m' l varg' (NOREP: norep fl),
    regset_related (construct_inj j bound fl) rs rs' ->
    mem_related j bound fl (strip m') m ->
    AsmLang.extcall_arg rs' m' l varg' ->
    exists varg, Asm.extcall_arg rs m l varg /\ val_related (construct_inj j bound fl) varg varg'.
Proof.
  intros. inv H1. eexists. split. constructor. auto.
  exploit loadv_related. eauto. eauto. apply offset_ptr_val_related. exact (H RSP).
  intro A. inv A. rewrite H3 in H4. discriminate.
  eexists. split. econstructor; eauto. rewrite H3 in H2. inv H2. auto.
Qed.

Lemma extcall_arg_fp_localize:
  forall j bound fl rs rs' l fp,
    Bset.inject j (fun b => Plt b bound) (fun b => Plt b bound) ->
    Bset.inj_inject (construct_inj j bound fl)->
    regset_related (construct_inj j bound fl) rs rs' ->
    extcall_arg_fp rs l fp ->
    exists fp', (extcall_arg_fp rs' l fp') /\ (FPlocalize (construct_inj j bound fl) fp' fp) /\
           fpG fl (fun b => Plt b bound) fp'.
Proof.
  intros. inv H2; eexists; split.
  econstructor. split; auto using fpG_emp, FPlocalize_emp.
  econstructor; eauto. split. apply loadv_fp_localize, offset_ptr_val_related; auto.
  destruct (H1 RSP); unfold loadv_fp, load_fp; simpl; red_blocks.
Qed.

Lemma extcall_arg_fp_localize':
  forall j rs rs' l fp',
    Bset.inj_inject j ->
    regset_related j rs rs' ->
    extcall_arg_fp rs' l fp' ->
    exists fp, (extcall_arg_fp rs l fp) /\ (FPlocalize j fp' fp).
Proof.
  intros. inv H1; eexists; split.
  econstructor. apply FPlocalize_emp.
  econstructor; eauto. apply loadv_fp_localize, offset_ptr_val_related; auto.
Qed.

Lemma extcall_arguments_related:
  forall j bound fl rs rs' m m' sig vargs (NOREP: norep fl),
    regset_related (construct_inj j bound fl) rs rs' ->
    mem_related j bound fl (strip m') m ->
    Asm.extcall_arguments rs m sig vargs ->
    exists vargs', AsmLang.extcall_arguments rs' m' sig vargs' /\
              list_forall2 (val_related  (construct_inj j bound fl)) vargs vargs'.
Proof.
  intros until sig. unfold Asm.extcall_arguments, AsmLang.extcall_arguments.
  generalize (Conventions1.loc_arguments sig). clear. induction l; intros.
  inv H1. eexists. split. constructor. constructor.
  inv H1. exploit IHl; eauto. intros [vargs'' [EVAL' REL']].
  destruct a. inv H4. exploit extcall_arg_related; eauto. intros [varg' [EVAL REL]].
  eexists. split; econstructor; eauto. constructor. auto.
  inv H4. exploit extcall_arg_related; try exact H3; eauto.
  exploit extcall_arg_related; try exact H7; eauto.
  intros [vlo' [EVAl1 REL1]] [vhi' [EVAL2 REL2]].
  eexists. split; repeat econstructor; eauto.
  inv REL1; inv REL2; simpl; auto.
Qed.

Lemma extcall_arguments_related':
  forall j bound fl rs rs' m m' sig vargs' (NOREP: norep fl),
    regset_related (construct_inj j bound fl) rs rs' ->
    mem_related j bound fl (strip m') m ->
    AsmLang.extcall_arguments rs' m' sig vargs' ->
    exists vargs, Asm.extcall_arguments rs m sig vargs /\
             list_forall2 (val_related  (construct_inj j bound fl)) vargs vargs'.
Proof.
  intros until sig. unfold Asm.extcall_arguments, AsmLang.extcall_arguments.
  generalize (Conventions1.loc_arguments sig). clear. induction l; intros.
  inv H1. eexists. split. constructor. constructor.
  inv H1. exploit IHl; eauto. intros [vargs'' [EVAL' REL']].
  destruct a. inv H4. exploit extcall_arg_related'; eauto. intros [varg' [EVAL REL]].
  eexists. split; econstructor; eauto. constructor. auto.
  inv H4. exploit extcall_arg_related'; try exact H3; eauto.
  exploit extcall_arg_related'; try exact H7; eauto.
  intros [vlo' [EVAl1 REL1]] [vhi' [EVAL2 REL2]].
  eexists. split; repeat econstructor; eauto.
  inv REL1; inv REL2; simpl; auto.
Qed.

Lemma extcall_args_fp_localize:
  forall j bound fl rs rs' sig fp,
    Bset.inject j (fun b => Plt b bound) (fun b => Plt b bound) ->
    Bset.inj_inject (construct_inj j bound fl)->
    regset_related (construct_inj j bound fl) rs rs' ->
    extcall_arguments_fp rs sig fp ->
    exists fp', (extcall_arguments_fp rs' sig fp') /\ (FPlocalize (construct_inj j bound fl) fp' fp) /\
           fpG fl (fun b => Plt b bound) fp'.
Proof.
  intros until sig. unfold extcall_arguments_fp. generalize (Conventions1.loc_arguments sig). clear.
  induction l; intros. inv H2. eexists. split; [econstructor| split; auto using FPlocalize_emp, fpG_emp].
  inv H2. exploit IHl; eauto. intros [fp' [EVAL' [REL' FPG']]].
  destruct a; inv H5. exploit extcall_arg_fp_localize; eauto. intros [fp1' [EVAL1 [REL1 FPG1]]].
  eexists. split. repeat econstructor; eauto. split; auto using FPlocalize_union, fpG_union.
  exploit extcall_arg_fp_localize; try exact H4; eauto. intros [fp1' [EVAL1 [REL1 FPG1]]].
  exploit extcall_arg_fp_localize; try exact H7; eauto. intros [fp2' [EVAL2 [REL2 FPG2]]].
  eexists. split. repeat econstructor; eauto. split; auto using FPlocalize_union, fpG_union.
Qed.

Lemma extcall_args_fp_localize':
  forall j rs rs' sig fp',
    Bset.inj_inject j ->
    regset_related j rs rs' ->
    extcall_arguments_fp rs' sig fp' ->
    exists fp, (extcall_arguments_fp rs sig fp) /\ (FPlocalize j fp' fp).
Proof.
  intros until sig. unfold extcall_arguments_fp. generalize (Conventions1.loc_arguments sig). clear.
  induction l; intros. inv H1; eexists; split. econstructor. auto using FPlocalize_emp.
  inv H1. exploit IHl; eauto. intros [fp' [EVAL' REL']].
  destruct a; inv H4. exploit extcall_arg_fp_localize'; eauto. intros [fp1' [EVAL1 REL1 ]].
  eexists. split. repeat econstructor; eauto. auto using FPlocalize_union.
  exploit extcall_arg_fp_localize'; try exact H3; eauto. intros [fp1' [EVAL1 REL1]].
  exploit extcall_arg_fp_localize'; try exact H6; eauto. intros [fp2' [EVAL2 REL2]].
  eexists. split. repeat econstructor; eauto. auto using FPlocalize_union.
Qed.

(** store args *)
Lemma store_args_related:
  forall j bound fl stk stk' args args' tys m m' (NOREP: norep fl),
    mem_related j bound fl (strip m') m ->
    construct_inj j bound fl stk = Some stk' ->
    list_forall2 (val_related (construct_inj j bound fl)) args args' ->
    option_rel (fun m fm => mem_related j bound fl (strip fm) m)
               (loadframe.store_args m stk args tys)
               (loadframe.store_args_fmem m' stk' args' tys).
Proof.
  unfold loadframe.store_args_fmem, loadframe.store_args.
  intros until tys. generalize 0. revert args' tys. induction args; intros.
  inv H1. simpl. destruct tys; constructor; auto.
  inv H1. destruct tys. simpl. constructor.
  inv H4; destruct t; simpl; unfold loadframe.store_stack, Mach.store_stack, loadframe.store_stack_fmem;
    simpl; try constructor;
      repeat match goal with
             | H: mem_related _ _ _ (strip ?m') ?m |- context[Memory.Mem.store ?chunk ?m stk (Ptrofs.unsigned ?ofs) ?v] =>
               exploit (storev_related j bound fl m m' (Vptr stk ofs) (Vptr stk' ofs) v); eauto; intro A; inv A; clear H
             | H: None = ?x, H1: None = ?y |- _ => rewrite <- H, <- H1; constructor; auto; fail
             | H: Some _ = _, H1: Some _ = _ |- _ => rewrite <- H, <- H1; eauto; fail
             end.
  rewrite <- H1, <- H2.
  exploit (storev_related j bound fl x y). eauto. eauto. apply rel_ptr. eauto. apply rel_int. intro A.
  inv A. rewrite <- H, <- H4. constructor.
  rewrite <- H, <- H4. eauto.
Qed.

Lemma store_args_freelist_unchg:
  forall m stk args tys m',
    loadframe.store_args_fmem m stk args tys = Some m' ->
    FMemory.Mem.freelist m' = FMemory.Mem.freelist m /\
    FMemory.Mem.validblocks m' = FMemory.Mem.validblocks m.
Proof.
  unfold loadframe.store_args_fmem. intros until args. generalize 0. revert m stk. induction args; simpl; intros.
  destruct tys; try discriminate. inv H. auto.
  destruct tys. discriminate. unfold loadframe.store_stack_fmem in *.
  destruct t; try discriminate;
    repeat match goal with
           | H: context[match Mem.storev _ _ _ _ with _ => _ end]|- _ =>
             destruct Mem.storev eqn:STOREV; try discriminate
           end;
    try (exploit IHargs; [eauto| intros [A B]; rewrite A, B ];
         unfold Mem.storev in STOREV; destruct Val.offset_ptr in STOREV; try discriminate;
         eauto using Mem.store_freelist, Mem.store_validblocks; fail).
  destruct a; try discriminate.
  unfold Mem.storev in *. destruct Val.offset_ptr; try discriminate. destruct Mem.store eqn:STORE; try discriminate.
  destruct Val.offset_ptr; try discriminate. destruct (Mem.store _ m0 b0 _ _) eqn:STORE'; try discriminate.
  try (exploit IHargs; [eauto| intros [A B]; rewrite A, B ]).
  split; eapply eq_trans; try eapply Mem.store_freelist; try eapply Mem.store_validblocks; eauto.
Qed.


Lemma store_args_fp_localize:
  forall j bound fl stk stk' tyl,
    Bset.inject j (fun b => Plt b bound) (fun b => Plt b bound) ->
    Bset.inj_inject (construct_inj j bound fl) ->
    construct_inj j bound fl stk = Some stk' ->
    FPlocalize (construct_inj j bound fl) (loadframe.store_args_fp stk' tyl) (loadframe.store_args_fp stk tyl) /\
    fpG fl (fun b => Plt b bound) (loadframe.store_args_fp stk' tyl).
Proof.
  intros until 3. unfold loadframe.store_args_fp. generalize 0. induction tyl; intros; simpl.
  auto using FPlocalize_emp, fpG_emp.
  specialize (IHtyl (z + typesize a)). destruct IHtyl.
  destruct a; simpl;
    try (split; [apply FPlocalize_union; auto;
                 unfold loadframe.store_stack_fp; apply storev_fp_localize; auto; apply offset_ptr_val_related; auto
                |apply fpG_union; auto; red_blocks]).
  try (split; [repeat apply FPlocalize_union; auto;
               unfold loadframe.store_stack_fp; apply storev_fp_localize; auto; apply offset_ptr_val_related; auto
              |apply fpG_union; auto; red_blocks]).
Qed.

(** exec lock prefixed instr *)
Lemma exec_locked_instr_related:
  forall j ge ge' i rs rs' m m' fl bound,
    fl = FMemory.Mem.freelist m' ->
    norep fl ->
    no_overlap fl (fun b : block => Plt b bound) ->
    (Bset.inject j (fun b => Plt b bound) (fun b => Plt b bound)) ->
    (forall id, option_rel (fun b b' => (construct_inj j bound fl) b = Some b') (Genv.find_symbol ge id) (Genv.find_symbol ge' id)) ->
    regset_related (construct_inj j bound fl) rs rs' ->
    mem_related j bound fl (strip m') m ->
    outcome_related j bound fl (ASM_local.exec_locked_instr ge i rs m) (AsmLang.exec_locked_instr ge' i rs' m') /\
    FPlocalize (construct_inj j bound fl) (AsmLang.exec_locked_instr_fp ge' i rs' m')
               (ASM_local.exec_locked_instr_fp ge i rs m) /\
    fpG fl (fun b => Plt b bound) (AsmLang.exec_locked_instr_fp ge' i rs' m').
Proof.
  intros. destruct i; simpl; auto using Stuck_related, FPlocalize_emp, fpG_emp.
  (** load *)
  split. apply exec_load_related; auto. apply construct_inj_injective; auto.
  eauto using exec_load_fp_localize, exec_load_fp_fpG.
  (** xchg *)
  split. exploit loadv_related. eauto. eauto. apply eval_addrmode_related. apply construct_inj_injective; auto.
  auto. eauto. intro. inv H6. erewrite <- H8, <- H9. constructor. rewrite <- H7, <- H8.
  exploit storev_related. eauto. eauto. apply eval_addrmode_related. apply construct_inj_injective; auto. auto.
  eauto. exact (H4 rs0). intro A. inv A. rewrite <- H6, <- H. constructor.
  rewrite <- H6, <- H. constructor; unfold nextinstr; solv_rel.
  split. apply FPlocalize_union; auto using construct_inj_injective, loadv_fp_localize, storev_fp_localize.
  exploit eval_addrmode_related; eauto using construct_inj_injective. instantiate (1:= a); intro.
  unfold loadv_fp, storev_fp. apply fpG_union; inv H6; red_blocks.
  (** cas *)
  exploit eval_addrmode_related; eauto using construct_inj_injective. instantiate (1:= a). intro A.
  inv A; simpl; auto using Stuck_related, FPlocalize_emp, fpG_emp.
  exploit loadv_related. eauto. eauto. apply rel_ptr. eauto. instantiate (1:= ofs); instantiate (1:= Mint32). 
  intro A. inv A. fold (loadv_fp Mint32 (Vptr b ofs)) (loadv_fp Mint32 (Vptr b' ofs)).
  split. constructor. split. apply loadv_fp_localize; auto using construct_inj_injective. 
  simpl. unfold load_fp. red_blocks.
  exploit cmpu_bool_related. eauto. eauto. eauto. eauto. exact H10. exact (H4 RAX).
  instantiate (1:= Ceq). intro A. inv A. split. constructor.
  fold (loadv_fp Mint32 (Vptr b ofs)) (loadv_fp Mint32 (Vptr b' ofs))
       (storev_fp Mint32 (Vptr b ofs)) (storev_fp Mint32 (Vptr b' ofs)).
  split.
  repeat apply FPlocalize_union; auto using loadv_fp_localize, storev_fp_localize,
                                 cmpu_fp_localize, construct_inj_injective.
  simpl. unfold load_fp, store_fp. repeat apply fpG_union; try red_blocks.
  inv H10; simpl; unfold weak_valid_pointer_fp; destruct (H4 RAX); simpl; try red_blocks.
  fold (loadv_fp Mint32 (Vptr b ofs)) (loadv_fp Mint32 (Vptr b' ofs))
       (storev_fp Mint32 (Vptr b ofs)) (storev_fp Mint32 (Vptr b' ofs)).
  destruct y0. 
  exploit storev_related. eauto. eauto. apply rel_ptr. exact H8. exact (H4 rs0). instantiate (1:= ofs). instantiate (1:= Mint32).
  intro A. split. inv A. constructor. constructor; auto. unfold nextinstr; solv_rel.
  split.
  repeat apply FPlocalize_union; auto using loadv_fp_localize, storev_fp_localize,
                                 cmpu_fp_localize, construct_inj_injective.
  simpl. unfold load_fp, store_fp; inv H10; destruct (H4 RAX); simpl; unfold weak_valid_pointer_fp; simpl; try red_blocks.
  split. constructor; auto. unfold nextinstr; solv_rel.
  split.
  repeat apply FPlocalize_union; auto using loadv_fp_localize, storev_fp_localize,
                                 cmpu_fp_localize, construct_inj_injective.
  simpl. unfold load_fp, store_fp; inv H10; destruct (H4 RAX); simpl; unfold weak_valid_pointer_fp; simpl; try red_blocks.
Qed.

Lemma exec_locked_instr_freelist_unchg:
  forall ge i rs rs' m m',
    AsmLang.exec_locked_instr ge i rs m = AsmLang.Next rs' m' ->
    Mem.freelist m' = Mem.freelist m.
Proof.
  destruct i; simpl; try discriminate; intros.
  unfold AsmLang.exec_load in H. destruct Mem.loadv; inv H. auto.
  destruct Mem.loadv; try discriminate. destruct Mem.storev eqn:A; inv H.
  destruct (eval_addrmode ge a rs0); try discriminate. eapply Mem.store_freelist; eauto.
  destruct Mem.loadv; try discriminate.
  destruct Val.cmpu_bool; try discriminate.
  destruct b;[|inv H; auto]. destruct Mem.storev eqn:A; inv H.
  destruct (eval_addrmode ge a rs0); try discriminate. eapply Mem.store_freelist; eauto.
Qed.

(** match state *)
Inductive match_core (j: Bset.inj) : core -> core -> Prop :=
| match_state_intro:
    forall rs_local rs lf_local lf,
      regset_related j rs_local rs ->
      loadframe_related j lf_local lf ->
      match_core j (Core_State rs_local lf_local) (Core_State rs lf)
| match_state_callin:
    forall b b' args args' tys oty,
      j b = Some b' ->
      list_forall2 (val_related j) args args' ->
      match_core j (Core_CallstateIn b args tys oty) (Core_CallstateIn b' args' tys oty)
| match_state_callout:
    forall ef args rs lf args' rs' lf',
      list_forall2 (val_related j) args args' ->
      regset_related j rs rs' ->
      loadframe_related j lf lf' ->
      match_core j (Core_CallstateOut ef args rs lf) (Core_CallstateOut ef args' rs' lf')
| match_state_lockstate:
    forall rs rs' signal lf lf',
      regset_related j rs rs' ->
      loadframe_related j lf lf' ->
      match_core j (Core_LockState rs signal lf) (Core_LockState rs' signal lf').


Definition wdcu (cu: Asm_comp_unit) : Prop :=
  nodup_ef (cu_defs cu) = true /\ nodup_gd_ident (cu_defs cu) = true.

Theorem asm_lift: LangLift Asm_comp_unit wdcu AsmLang Asm_IS.
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
  intros jfull INCRJ INJECT.
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
    intros [args_local INJARGS].
    exists args_local. split.
    apply list_forall2_imply with (val_related jfull); auto. intros. apply val_related_val_inject_strict; auto.
    intros. unfold init_core, fundef_init in *.
    destruct (Genv.find_symbol ge_local id) eqn:FINDSYMB;[|discriminate].
    destruct (Genv.find_funct_ptr ge_local b) eqn:FINDDEF;[|discriminate].
    exploit (SYMBREL). instantiate (1:=id). unfold Senv.find_symbol; simpl.
    rewrite HGE in FINDSYMB. unfold ge_extend in FINDSYMB. unfold Genv.find_symbol in *. simpl in *. rewrite FINDSYMB.
    intro A. inversion A. clear A. subst bj b0. rename H4 into FBINJ. symmetry in H3. rename H3 into FINDSYMB'.
    exploit DEFSREL. exact FBINJ. intro A. unfold Genv.find_funct_ptr, Genv.find_def in *. rewrite <- A.
    rewrite HGE in FINDDEF. unfold ge_extend in FINDDEF. simpl in *.
    destruct ((Genv.genv_defs _)!b); [|discriminate].
    destruct g; [|discriminate]. inversion FINDDEF; subst f0; clear FINDDEF. destruct f; [|discriminate].
    destruct (wd_args args_local) eqn:WDARGS; [|discriminate]. inversion H0. subst lc; clear H0.
    eapply wd_args_inject with (j:=Bset.inj_to_meminj jfull) in WDARGS; eauto. rewrite WDARGS. eexists; split. eauto.
    Focus 2.
    generalize args_local INJARGS. clear. induction args; intros; inv INJARGS; constructor; auto.
    apply val_related_val_inject_strict in H2. inv H2; econstructor; eauto.
    
    intros m fl INITMEM NOREP NOOVERLAP RC.
    exploit lmem_construction; eauto. subst bound. auto.
    intros [lm [INITMEM_local MEMREL]]. exists lm.
    rewrite <- HBOUND in MEMREL. rewrite <- HBOUND at 1. rewrite HGE in INJECT; simpl in INJECT.
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
    constructor. unfold construct_inj. eapply inject_incr_bset_inj_incr in FBINJ; eauto. rewrite FBINJ.
    destruct plt; auto. exfalso. apply n. inv INJECT. inv inj_weak. eapply inj_dom'; eauto.
    eapply list_forall2_imply. eauto. intros. apply val_related_incr with jfull; auto.
    apply construct_inj_incr; auto. eapply Bset.inj_dom'. inv INJECT; eauto.
    apply bset_eq_no_overlap with (valid_block_bset m); auto.
    intro. rewrite HBOUND, <- init_mem_valid_block; eauto. tauto. }
  (** step *)
  { intros fl c lc m lm lfp lc' lm' [fm [STRIP [FL [_ [_ [MS [MEMREL [NOREP NOOVERLAP]]]]]]]] STEP.
    assert (FINDFUNCT: forall rs_local rs b ofs f,
               regset_related (construct_inj jfull bound fl) rs_local rs ->
               rs_local PC = Vptr b ofs ->
               Genv.find_funct_ptr ge_local b = Some f ->
               exists b', jfull b = Some b' /\
                     rs PC = Vptr b' ofs /\
                     Genv.find_funct_ptr ge b' = Some f).
    { intros. destruct (H PC); try discriminate. inv H0. unfold Genv.find_funct_ptr in *.
      destruct (Genv.find_def (ge_extend _ _ _) b) eqn:FIND; try discriminate.
      destruct g eqn:GD; try discriminate. inv H1.
      exploit Genv.genv_defs_range. eauto. unfold ge_extend. simpl. intro.
      unfold construct_inj in H2. destruct plt;[|contradiction].
      eexists. split. eauto. split. eauto. unfold Genv.find_def in *. 
      unfold ge_extend in FIND. simpl in FIND. erewrite <- DEFSREL, FIND. auto.
      apply DEFSDOM in FIND. destruct FIND. rewrite H1. f_equal.
      eapply inject_incr_bset_inj_incr in H1; eauto. rewrite H1 in H2. inv H2. auto. }
    assert (SYMBREL': forall id,
               option_rel (fun b b' => construct_inj jfull (Genv.genv_next ge) (FMemory.Mem.freelist fm) b = Some b')
                          (Senv.find_symbol
                             (ge_extend (Genv.globalenv (mkprogram (cu_defs cu) (cu_public cu) (1%positive)))
                                        bound GEBOUND) id)
                          (Senv.find_symbol ge id)).
    { intros. specialize (SYMBREL id).
      inv SYMBREL; unfold Senv.find_symbol; simpl in *; unfold Genv.find_symbol, ge_extend in *; simpl in *.
      rewrite <- H1, <- H. constructor. eapply inject_incr_bset_inj_incr.
      eapply construct_inj_incr. intros. eapply Bset.inj_dom' in H0; try (inv INJECT; eauto; fail); eauto.
      eapply inject_incr_bset_inj_incr; eauto.
      rewrite <- H1, <- H2. constructor. }
    inv MS; inv STEP.
    { (* exec instr step *)
      exploit FINDFUNCT; eauto; intros [b' [FBINJ [HPC FIND']]].
      exploit exec_instr_related. auto. exact NOREP. exact NOOVERLAP. exact INJECT. exact SYMBREL'.
      eauto. eauto. erewrite H6. intros [OUTCOMREL [FPREL FPG]]. inv OUTCOMREL.
      do 3 eexists. split. econstructor. instantiate (1:= fm). constructor; auto.
      eapply AsmLang.exec_step_internal; eauto. eauto. split. auto.
      split. auto. exists m'. split. auto. split. eapply exec_instr_fl_unchanged; eauto.
      split. auto. split. auto. split. constructor; auto. auto.
    }
    { (* i64ext builtins *)
      exploit FINDFUNCT; eauto; intros [b' [FBINJ [HPC FIND']]].
      exploit eval_builtin_args_related; eauto. intros [vargs' [EVAL' ARGSREL]].
      exploit eval_builtin_args_fp_localize; try exact H7; eauto. intros [fp' [FPEVAL [FPREL FPG]]].
      exploit helpers.i64ext_args_related; eauto. apply helpers.i64ext_extcall.
      split. eauto. intros. eapply helpers.i64ext_irr; eauto.
      intros [res' [BUILTINSEM RESREL]].
      do 3 eexists. split. econstructor; eauto. econstructor; eauto. 
      eapply AsmLang.exec_step_builtin; eauto.
      intro. apply H6. destruct (H RSP); auto; discriminate.
      split. auto. split. auto. exists fm.
      do 4 (split; auto). split; auto.
      constructor; auto. unfold nextinstr_nf, nextinstr. 
      apply set_regset_related; auto. apply offset_ptr_val_related.
      apply undef_regs_regset_related; auto.
    } 
    { (* step to ext *)
      exploit FINDFUNCT; eauto. intros [b' [FBINJ [HPC FIND']]].
      exploit extcall_arguments_related; eauto. intros [args' [EVAL ARGREL]].
      exploit extcall_args_fp_localize; eauto. apply construct_inj_injective; auto.
      unfold ge_extend. simpl. intros [fp' [EVALFP [RELFP FPG]]].
      do 3 eexists. split. econstructor; eauto. econstructor; eauto.
      eapply AsmLang.exec_step_to_external; eauto.
      split; auto. split; auto. exists fm. repeat (split; auto).
      constructor; auto.
    }
(*    { (* step to lock *)
      exploit FINDFUNCT; eauto. intros [b' [FBINJ [HPC FIND']]].
      do 3 eexists. split. econstructor; eauto. econstructor; eauto.
      eapply AsmLang.exec_step_to_lock; eauto.
      repeat (split; auto using FPlocalize_emp, fpG_emp).
      exists fm. repeat (split; auto). constructor; auto.
    } *)
    { (* init call *)
      destruct (FMemory.Mem.alloc fm 0 (4 * z)) as (fm1, stk') eqn:ALLOC'.
      exploit alloc_related; eauto. exploit alloc_result_related; eauto. intros STKREL MEMREL1.
      exploit store_args_related; eauto. intro A. inv A. rewrite H12 in H2. discriminate.
      rewrite H12 in H1. inversion H1. subst x. clear H1. rename y into fm2. rename H3 into MEMREL2.
      symmetry in H2; rename H2 into STOREARGS.
      exploit store_args_fp_localize; eauto using construct_inj_injective.
      unfold ge_extend; simpl. intros [FPREL FPG].
      do 3 eexists. split. do 2 econstructor; eauto.
      { generalize args' H0 tys z H5; clear. induction args; intros; inv H0; auto.
        simpl in *. intros. destruct tys; try discriminate.
        destruct (val_has_type_func a t) eqn:?; try discriminate.
        assert (val_has_type_func b1 t = true).
        { inv H2; destruct t; try discriminate; auto. }
        rewrite H. destruct (loadframe.args_len_rec args tys) eqn:?; try discriminate. inv H5.
        erewrite IHargs; eauto. }
      split. apply FPlocalize_union; eauto.
      unfold MemOpFP.alloc_fp, alloc_fp, uncheck_alloc_fp.
      constructor; simpl; try (constructor; tauto).
      
      constructor; intros. 
      erewrite <- Memory.Mem.alloc_result, <- FMemory.Mem.alloc_result; eauto.
      Locs.unfolds. do 2 destruct peq; try tauto; try congruence.
      subst. exfalso. apply n. eapply construct_inj_injective; eauto.
      split. apply fpG_union; eauto.
      unfold alloc_fp, uncheck_alloc_fp; erewrite <- FMemory.Mem.alloc_result; eauto.
      unfold fpG. right.
      eapply FMemory.Mem.alloc_result in ALLOC'; eauto.
      subst. unfold Bset.belongsto,FP.blocks,Locs.blocks in H1.
      destruct H1. eapply alloc_fp_loc in H1; eauto.
      exists fm2. split; auto. split. apply eq_trans with (Mem.freelist fm1).
      apply store_args_freelist_unchg in STOREARGS. tauto.
      eapply FMemory.Mem.alloc_freelist; eauto.
      repeat (split; auto). constructor; auto.
      subst rs0. repeat apply set_regset_related; auto. intro. unfold Pregmap.init; auto. solv_rel.
      simpl. split; auto.
    }
    { (* i64ext *)
      exploit FINDFUNCT; eauto. intros [b' [FPINJ [HPC FIND']]].
      exploit helpers.i64ext_args_related; eauto. apply helpers.i64ext_extcall.
      split. eauto. intros. eapply helpers.i64ext_irr; eauto.
      intros [res' [BUILTINSEM RESREL]].
      do 3 eexists. split. econstructor; eauto. econstructor; eauto. 
      eapply AsmLang.exec_step_i64ext; eauto.
      repeat (split; auto). apply fpG_emp. exists fm. repeat (split; auto).
      constructor; auto. unfold set_pair. destruct (loc_external_result); auto.
      inv RESREL; simpl; auto.
    }
(*    { (* exec locked instr *)
      exploit FINDFUNCT; eauto. intros [b' [FPINJ [HPC FIND']]].
      exploit exec_locked_instr_related; eauto. exact SYMBREL'.
      rewrite H11. intros [OUTCOMREL [FPREL FPG]]. inv OUTCOMREL.
      do 3 eexists. split. econstructor; eauto. econstructor; eauto.
      eapply AsmLang.exec_step_locked; eauto. repeat (split; auto).
      exists m'. split; auto. split. eapply exec_locked_instr_freelist_unchg; eauto.
      repeat (split; auto). constructor; auto.
    } *)
  }
  (** At_ext *)
  {  intros fl c lc m lm f sg args_local [fm [STRIP [FL [_ [_ [MS [MEMREL [NOREP NOOVERLAP]]]]]]]] ATEXT.
     unfold at_external in *. inv MS; try discriminate.
     (** ef *)
     destruct ef; try discriminate.
     destruct (invert_symbol_from_string _ name) eqn:NAME; try discriminate.
     erewrite invert_symbol_from_string_eq. rewrite NAME. 
     destruct peq; simpl in *. discriminate.
     destruct peq; simpl in *. discriminate.
     inv ATEXT.
     eexists. split. eauto. unfold args_related.
     { generalize args_local args' H H2; clear. induction args_local; intros; inv H; inv H2; constructor; auto.
       inv H3; econstructor. unfold Bset.inj_to_meminj, construct_inj in *. 
       destruct plt; try contradiction. rewrite H. eauto. rewrite Ptrofs.add_zero. auto. }
     (** TODO: missing norep gd in Localize/Lift *)
     { destruct WDCU. eapply nodup_ef_ge_norep_ef_name; try eassumption.
       econstructor. eauto. eauto. }
     { destruct WDCU. eapply nodup_gd_init_genv_ident_exists; eauto.
       econstructor. eauto. eauto. }
     econstructor; eauto. unfold ge_extend; simpl. auto with coqlib.
     (** lock *)
     (* destruct signal; inv ATEXT.
     eexists. split; eauto. constructor.
     eexists. split; eauto. constructor. *)
  }
  (** after_ext *)
  { intros fl c lc m lm ores lc' lores [fm [STRIP [FL [_ [_ [MS [MEMREL [NOREP NOOVERLAP]]]]]]]] RESREL AFTEXT.
    unfold after_external in *. inv MS; try discriminate.
    (** ef *)
    destruct ef; try discriminate. destruct lores, ores; simpl in *; try contradiction.
    { destruct (sig_res sg) as [ty|];
        [destruct (val_has_type_func v ty) eqn:TYPE, (val_has_type_func v0 ty) eqn:TYPE'
        |]; try discriminate.
      eexists. split. eauto. exists fm. repeat (split; auto). inv AFTEXT. constructor; auto.
      unfold set_pair. destruct (loc_external_result sg).
      repeat apply set_regset_related; auto.
      inv RESREL; try constructor. unfold Bset.inj_to_meminj in H2. destruct (jfull b1) eqn:Jb1; inv H2.
      rewrite Ptrofs.add_zero. constructor. unfold construct_inj. rewrite Jb1. destruct plt; auto.
      exfalso. eapply Bset.inj_dom' in Jb1; inv INJECT; eauto. eapply n. eauto.
      repeat apply set_regset_related; inv RESREL; simpl; auto.
      revert TYPE TYPE' RESREL; clear. intros; exfalso. inv RESREL; destruct ty; simpl in *; discriminate. }
    { destruct (sig_res sg) as [ty|]; try discriminate.
      eexists. split. eauto. exists fm. repeat (split; auto). inv AFTEXT. constructor; auto.
      unfold set_pair. destruct (loc_external_result sg). repeat apply set_regset_related; auto. simpl. auto. }
    (** lock *)
    (* destruct signal, lores, ores; try contradiction; inv AFTEXT.
    { eexists. split. eauto. exists fm. repeat (split; auto). constructor; auto. }
    { eexists. split. eauto. exists fm. repeat (split; auto). constructor; auto. } *)
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
    unfold halted, Vzero; intros fl c lc m lm lres [fm [STRIP [FL [_ [_ [MS [MEMREL [NOREP NOOVERLAP]]]]]]]] HALT GRES.
    inv MS; try discriminate. destruct lf_local, lf. inv H0.
    destruct (H PC); try discriminate. destruct Val.cmp_bool; try discriminate.
    simpl in *. destruct (Conventions1.loc_result); inv HALT.
    eexists. split. eauto.
    destruct (H (preg_of r)); try constructor. econstructor. unfold Bset.inj_to_meminj, construct_inj in H0|- * .
    destruct (plt b0 _). rewrite H0. eauto. exfalso. eauto. rewrite Ptrofs.add_zero; auto.
    eexists. split. eauto.
    destruct (H (preg_of rhi)), (H (preg_of rlo)); try constructor.
    Unshelve. exact 0.
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

Theorem asm_localize: LangLocalize Asm_comp_unit wdcu AsmLang Asm_IS.
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

    intros. unfold init_core, fundef_init in *.
    destruct (Genv.find_symbol ge id) eqn:FINDSYMB;[|discriminate].
    destruct (Genv.find_funct_ptr ge b) eqn:FINDDEF;[|discriminate].
    exploit (SYMBREL). instantiate (1:=id). unfold Senv.find_symbol; simpl.
    rewrite FINDSYMB. intro. inv H1. symmetry in H2.
    unfold Genv.find_symbol in H2 |- * .  simpl. rewrite H2. clear H2.
    exploit DEFSREL. exact H5. unfold Genv.find_funct_ptr, Genv.find_def in *.
    destruct ((Genv.genv_defs ge)!b) eqn:FINDDEF'; try discriminate. intro.
    simpl. rewrite H1. clear H1. rewrite FINDDEF. 
    destruct g; [|discriminate]. inversion FINDDEF; subst f0; clear FINDDEF. destruct f; [|discriminate].
    destruct (wd_args args) eqn:WDARGS; [|discriminate].
    assert (wd_args args_local (sig_args (fn_sig f)) = true).
    { generalize (sig_args (fn_sig f)) INJARGS WDARGS. clear. intros until 1. unfold wd_args.
      intro. apply andb_true_iff in WDARGS. destruct WDARGS.
      apply andb_true_iff in H. destruct H.
      apply andb_true_iff. split. apply andb_true_iff. split.
      (* *)
      clear H1 H0. revert l H. induction INJARGS. auto.
      intros. destruct l. inversion H0. simpl in *. apply andb_true_iff in H0. destruct H0.
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
    inv H0. constructor. unfold construct_inj. eapply inject_incr_bset_inj_incr in H5; eauto. rewrite H5.
    destruct plt; auto. exfalso. apply n. inv INJECT. inv inj_weak. eapply inj_dom'; eauto.
    eapply list_forall2_imply. eauto. intros. apply val_related_incr with jfull; auto.
    apply construct_inj_incr; auto. eapply Bset.inj_dom'. inv INJECT; eauto.
    apply bset_eq_no_overlap with (valid_block_bset m); auto.
    intro. rewrite  <- init_mem_valid_block; eauto. tauto. }
  (** step *)
  { intros fl c lc m lm lfp lc' lm' [fm [STRIP [FL [_ [_ [MS [MEMREL [NOREP NOOVERLAP]]]]]]]] STEP FPG.
    assert (FINDFUNCT: forall rs_local rs b' ofs f,
               regset_related (construct_inj jfull bound fl) rs_local rs ->
               rs PC = Vptr b' ofs ->
               Genv.find_funct_ptr ge b' = Some f ->
               exists b, jfull b = Some b' /\
               rs_local PC = Vptr b ofs /\
               Genv.find_funct_ptr ge_local b = Some f).
    { intros. destruct (H PC); try discriminate. inv H0. unfold Genv.find_funct_ptr in *.
      destruct (Genv.find_def) eqn:FIND; try discriminate.
      destruct g eqn:GD; try discriminate. inv H1.
      exploit Genv.genv_defs_range. eauto. unfold ge_extend. unfold Genv.find_def in *. simpl. intro.
      unfold construct_inj in H2. destruct plt.
      eexists. split. eauto. split. eauto. pose proof GEMATCH. eapply ge_match_strict_defs in GEMATCH; eauto.
      rewrite FIND in GEMATCH. inv GEMATCH. inv H5.
      exploit DEFSDOM. eauto. intros [b'' INJ]. pose proof INJ.
      eapply inject_incr_bset_inj_incr in H3; eauto. rewrite H2 in H3. inv H3.
      f_equal. erewrite DEFSREL in H4; eauto. rewrite FIND in H4. inv H4. auto.

      exfalso. inv H2. eapply NOOVERLAP; eauto.
    }
    assert (SYMBREL': forall id,
               option_rel (fun b b' => construct_inj jfull (Genv.genv_next ge) (FMemory.Mem.freelist fm) b = Some b')
                          (Senv.find_symbol
                             (ge_extend (Genv.globalenv (mkprogram (cu_defs cu) (cu_public cu) (1%positive)))
                                        bound GEBOUND) id)
                          (Senv.find_symbol ge id)).
    { intros. specialize (SYMBREL id).
      inv SYMBREL; unfold Senv.find_symbol; simpl in *; unfold Genv.find_symbol, ge_extend in *; simpl in *.
      rewrite <- H1, <- H. constructor. eapply inject_incr_bset_inj_incr.
      eapply construct_inj_incr. intros. eapply Bset.inj_dom' in H0; try (inv INJECT; eauto; fail); eauto.
      eapply inject_incr_bset_inj_incr; eauto.
      rewrite <- H1, <- H2. constructor. }
    inv MS; inv STEP.
    inv H2.
    { (* exec instr step *)
      exploit FINDFUNCT; eauto; intros [b' [FBINJ [HPC FIND']]].
      exploit exec_instr_related. auto. exact NOREP. exact NOOVERLAP. exact INJECT. exact SYMBREL'.
      eauto. eauto. apply embed_eq in H1. subst fm. erewrite H8.
      intros [OUTCOMREL [FPREL FPG']]. inv OUTCOMREL.
      do 3 eexists. split. econstructor; eauto.
      split. auto. exists m'. split. auto. split. eapply exec_instr_fl_unchanged; eauto.
      split. auto. split. auto. split. constructor; auto. auto.
    }
    { (* i64ext builtins *)
      apply embed_eq in H1. subst fm.
      exploit FINDFUNCT; eauto; intros [b' [FBINJ [HPC FIND']]].
      exploit eval_builtin_args_related'; eauto. intros [vargs' [EVAL' ARGSREL]].
      exploit eval_builtin_args_fp_localize'; try exact H9; try exact H; eauto.
      eapply construct_inj_injective; eauto.
      intros [fp' [FPEVAL FPREL]].
      exploit helpers.i64ext_args_related'; try exact H11. eauto. 
      intros [res' [BUILTINSEM RESREL]].
      do 3 eexists. split.
      apply helpers.i64ext_extcall in BUILTINSEM. destruct BUILTINSEM.
      eapply exec_step_builtin; eauto.
      intro. apply H8. destruct (H RSP); auto; discriminate.
      split; auto. exists m'.
      do 4 (split; auto). split; auto.
      constructor; auto. unfold nextinstr_nf, nextinstr. 
      apply set_regset_related; auto. apply offset_ptr_val_related.
      apply undef_regs_regset_related; auto.
    } 
    { (* step to ext *)
      apply embed_eq in H1. subst m'.
      exploit FINDFUNCT; eauto. intros [b' [FBINJ [HPC FIND']]].
      exploit extcall_arguments_related'; eauto. intros [args' [EVAL ARGREL]].
      exploit extcall_args_fp_localize'; try exact H; eauto. apply construct_inj_injective; auto.
      simpl. intros [fp' [EVALFP RELFP]].
      do 3 eexists. split. eapply exec_step_to_external; eauto. 
      split; auto. exists fm. repeat (split; auto).
      constructor; auto.
    }
(*    { (* step to lock *)
      apply embed_eq in H1. subst m'.
      exploit FINDFUNCT; eauto. intros [b' [FBINJ [HPC FIND']]].
      do 3 eexists. split. eapply exec_step_to_lock; eauto.
      repeat (split; auto using FPlocalize_emp, fpG_emp).
      exists fm. repeat (split; auto). constructor; auto.
    } *)
    inv H2.
    { (* init call *)
      apply embed_eq in H1. subst m.
      destruct (Memory.Mem.alloc lm 0 (4 * z)) as (lm1, stk') eqn:ALLOC'.
      exploit alloc_related; eauto. exploit alloc_result_related; eauto. intros STKREL MEMREL1.
      exploit store_args_related; eauto. intro A. inv A. rewrite H14 in H3. discriminate.
      rewrite H14 in H2. inversion H2. subst y. clear H2. rename x into lm2. rename H3 into MEMREL2.
      symmetry in H1; rename H1 into STOREARGS.
      exploit store_args_fp_localize; eauto using construct_inj_injective.
      intros [FPREL FPG'].
      do 3 eexists. split. econstructor; eauto.
      { generalize args' H0 tys z H7; clear. induction args; intros; inv H0; auto.
        simpl in *. destruct tys; try discriminate.
        destruct (val_has_type_func b1 t) eqn:?; try discriminate.
        assert (val_has_type_func a t = true).
        { inv H2; destruct t; try discriminate; auto. }
        rewrite H. destruct (loadframe.args_len_rec bl tys) eqn:?; try discriminate. 
        erewrite IHargs; eauto. }
      split. apply FPlocalize_union; eauto.
      unfold MemOpFP.alloc_fp, alloc_fp, uncheck_alloc_fp.
      constructor; simpl; try (constructor; tauto).
      
      constructor; intros. 
      erewrite <- Memory.Mem.alloc_result, <- FMemory.Mem.alloc_result; eauto.
      Locs.unfolds. do 2 destruct peq; try tauto; try congruence.
      subst. exfalso. apply n. eapply construct_inj_injective; eauto.
      exists m'. split; auto. split. apply eq_trans with (Mem.freelist m1).
      apply store_args_freelist_unchg in H14. tauto.
      eapply FMemory.Mem.alloc_freelist; eauto.
      repeat (split; auto). constructor; auto.
      subst rs0. repeat apply set_regset_related; auto. intro. unfold Pregmap.init; auto. solv_rel.
      simpl. split; auto.
    }
    inv H3.
    { (* i64ext *)
      apply (embed_eq) in H2. subst.
      exploit FINDFUNCT; eauto. intros [b' [FPINJ [HPC FIND']]].
      exploit helpers.i64ext_args_related'; eauto.
      intros [res' [BUILTINSEM RESREL]].
      apply helpers.i64ext_extcall in BUILTINSEM. destruct BUILTINSEM.
      do 3 eexists. split. eapply exec_step_i64ext; eauto.
      repeat (split; auto). exists fm. repeat (split; auto).
      constructor; auto. unfold set_pair. destruct (loc_external_result); auto.
      inv RESREL; simpl; auto.
    }
    inv H2.
(*    { (* exec locked instr *)
      apply embed_eq in H1. subst.
      exploit FINDFUNCT; eauto. intros [b' [FPINJ [HPC FIND']]].
      exploit exec_locked_instr_related; eauto. exact SYMBREL'.
      rewrite H13. intros [OUTCOMREL [FPREL FPG']]. inv OUTCOMREL.
      do 3 eexists. split.  eapply exec_step_locked; eauto. repeat (split; auto).
      exists m'. split; auto. split. eapply exec_locked_instr_freelist_unchg; eauto.
      repeat (split; auto). constructor; auto.
    } *)
  }
  (** At_ext *)
  {  intros fl c lc m lm f sg args_local [fm [STRIP [FL [_ [_ [MS [MEMREL [NOREP NOOVERLAP]]]]]]]] ATEXT GARGS.
     unfold at_external in *. inv MS; try discriminate.
     (** ef *)
     destruct ef; try discriminate.
     destruct (invert_symbol_from_string _ name) eqn:NAME; try discriminate.
     erewrite <-invert_symbol_from_string_eq. rewrite NAME.
     destruct peq; simpl in *. discriminate.
     destruct peq; simpl in *. discriminate.
     inv ATEXT.
     eexists. split. eauto. unfold args_related.
     { generalize args_local args H GARGS NOOVERLAP; clear. induction args_local; intros; inv H; inv GARGS; constructor; auto.
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
     (** lock *)
     (* destruct signal; inv ATEXT.
     eexists. split; eauto. constructor.
     eexists. split; eauto. constructor. *)
  }
  (** after_ext *)
  { intros fl c lc m lm ores lc' lores [fm [STRIP [FL [_ [_ [MS [MEMREL [NOREP NOOVERLAP]]]]]]]] RESREL AFTEXT.
    unfold after_external in *. inv MS; try discriminate.
    (** ef *)
    destruct ef; try discriminate. destruct lores, ores; simpl in *; try contradiction.
    { destruct (sig_res sg) as [ty|];
        [destruct (val_has_type_func v ty) eqn:TYPE, (val_has_type_func v0 ty) eqn:TYPE'
        |]; try discriminate.
      eexists. split. eauto. exists fm. repeat (split; auto). inv AFTEXT. constructor; auto.
      unfold set_pair. destruct (loc_external_result sg).
      repeat apply set_regset_related; auto.
      inv RESREL; try constructor. unfold Bset.inj_to_meminj in H2. destruct (jfull b1) eqn:Jb1; inv H2.
      rewrite Ptrofs.add_zero. constructor. unfold construct_inj. rewrite Jb1. destruct plt; auto.
      exfalso. eapply Bset.inj_dom' in Jb1; inv INJECT; eauto. eapply n. eauto.
      repeat apply set_regset_related; inv RESREL; simpl; auto.
      revert TYPE TYPE' RESREL; clear. intros; exfalso. inv RESREL; destruct ty; simpl in *; discriminate. }
    { destruct (sig_res sg) as [ty|]; try discriminate.
      eexists. split. eauto. exists fm. repeat (split; auto). inv AFTEXT. constructor; auto.
      unfold set_pair. destruct (loc_external_result sg). repeat apply set_regset_related; auto. simpl. auto. }
    (** lock *)
    (* destruct signal, lores, ores; try contradiction; inv AFTEXT.
    { eexists. split. eauto. exists fm. repeat (split; auto). constructor; auto. }
    { eexists. split. eauto. exists fm. repeat (split; auto). constructor; auto. } *)
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
    unfold halted, Vzero; intros fl c lc m lm lres [fm [STRIP [FL [_ [_ [MS [MEMREL [NOREP NOOVERLAP]]]]]]]] HALT GRES.
    inv MS; try discriminate. destruct lf_local, lf. inv H0.
    destruct (H PC); try discriminate. destruct Val.cmp_bool; try discriminate.
    simpl in *. destruct (Conventions1.loc_result); inv HALT.
    eexists. split. eauto.
    destruct (H (preg_of r)); try constructor. econstructor. unfold Bset.inj_to_meminj, construct_inj in H0|- * .
    destruct (plt b0 _). rewrite H0. eauto. exfalso. inv H0. eapply NOOVERLAP; eauto.
    rewrite Ptrofs.add_zero; auto.
    eexists. split. eauto.
    destruct (H (preg_of rhi)), (H (preg_of rlo)); try constructor.
    Unshelve. exact 0.
  }
Qed.