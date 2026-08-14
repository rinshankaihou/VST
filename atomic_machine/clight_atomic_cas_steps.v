(** Local Clight paths through the concrete [atomic_CAS] wrapper. *)

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Values.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Cop.
Require Import compcert.cfrontend.Clight.

Require Import compcert.concurrency.common.FMemory.
Require Import compcert.concurrency.common.Footprint.
Require Import compcert.concurrency.common.GAST.
Require Import compcert.concurrency.common.InteractionSemantics.
Require Import compcert.concurrency.comp_correct.ClightLang.

Require Import atomic_machine.clight_is2_markers.
Require Import atomic_machine.clight_atomic_wrappers.
Require Import atomic_machine.clight_atomic_wrapper_steps.

From Stdlib Require Import List.
Import ListNotations.

Module ClightAtomicCASSteps.

  Import ClightAtomicWrappers.
  Import ClightAtomicWrapperSteps.

  Definition cas_test : expr :=
    Ebinop Cop.Oeq old_expr expected_expr tint.

  Definition cas_success_statement : statement :=
    Ssequence (Sassign target_lvalue new_expr)
      (Sset result_temp (Econst_int Int.one tint)).

  Definition cas_failure_statement : statement :=
    Sset result_temp (Econst_int Int.zero tint).

  Definition cas_branch_statement : statement :=
    Sifthenelse cas_test cas_success_statement cas_failure_statement.

  Definition cas_exit_tail : statement :=
    Ssequence exit_atomic (Sreturn (Some result_expr)).

  Definition cas_body_tail : statement :=
    Ssequence (Sset old_temp target_lvalue)
      (Ssequence cas_branch_statement cas_exit_tail).

  Definition cas_return_statement : statement :=
    Sreturn (Some result_expr).

  Definition cas_ent_cont (le : temp_env) : cont :=
    Kcall None atomic_CAS_function empty_env le
      (Kseq cas_body_tail Kstop).

  Definition cas_ext_cont (le : temp_env) : cont :=
    Kcall None atomic_CAS_function empty_env le
      (Kseq cas_return_statement Kstop).

  Definition cas_success_store_cont : cont :=
    Kseq (Sset result_temp (Econst_int Int.one tint))
      (Kseq cas_exit_tail Kstop).

  Definition cas_success_assign_state (le : temp_env) : ClightLang.core :=
    ClightLang.Core_State atomic_CAS_function
      (Sassign target_lvalue new_expr)
      cas_success_store_cont empty_env le.

  Definition cas_success_after_assign_state
      (le : temp_env) : ClightLang.core :=
    ClightLang.Core_State atomic_CAS_function Sskip
      cas_success_store_cont empty_env le.

  Lemma CAS_entry_target_lookup p expected new :
    (CAS_entry_temps p expected new) ! target_temp = Some p.
  Proof.
    unfold CAS_entry_temps.
    rewrite PTree.gso by discriminate.
    rewrite PTree.gso by discriminate.
    apply PTree.gss.
  Qed.

  Lemma CAS_entry_expected_lookup p expected new :
    (CAS_entry_temps p expected new) ! expected_temp = Some expected.
  Proof.
    unfold CAS_entry_temps.
    rewrite PTree.gso by discriminate.
    apply PTree.gss.
  Qed.

  Lemma CAS_entry_new_lookup p expected new :
    (CAS_entry_temps p expected new) ! new_temp = Some new.
  Proof. unfold CAS_entry_temps. apply PTree.gss. Qed.

  Lemma sem_CAS_eq_true ge m n :
    FCop.sem_binary_operation ge.(Clight.genv_cenv) Cop.Oeq
      (Vint n) tint (Vint n) tint m = Some Vtrue.
  Proof.
    unfold FCop.sem_binary_operation, FCop.sem_cmp, FCop.sem_binarith,
      FCop.sem_cast, Cop.classify_cmp, Cop.classify_binarith,
      Cop.binarith_type, Cop.classify_cast, tint.
    destruct Archi.ptr64; simpl;
      rewrite Int.eq_true; reflexivity.
  Qed.

  Lemma sem_CAS_eq_false ge m n1 n2 (Hneq : n1 <> n2) :
    FCop.sem_binary_operation ge.(Clight.genv_cenv) Cop.Oeq
      (Vint n1) tint (Vint n2) tint m = Some Vfalse.
  Proof.
    unfold FCop.sem_binary_operation, FCop.sem_cmp, FCop.sem_binarith,
      FCop.sem_cast, Cop.classify_cmp, Cop.classify_binarith,
      Cop.binarith_type, Cop.classify_cast, tint.
    destruct Archi.ptr64; simpl;
      rewrite Int.eq_false by exact Hneq; reflexivity.
  Qed.

  Lemma atomic_CAS_to_ent
      (ge : Clight.genv) (m : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (expected new : int)
      (ent_block : block)
      (Hent_symbol :
        Genv.find_symbol ge GAST.ent_atom = Some ent_block)
      (Hent_fun :
        Genv.find_funct_ptr ge ent_block = Some ent_atom_external) :
    let le := CAS_entry_temps
      (Vptr b ofs) (Vint expected) (Vint new) in
    fstep2_star ge m
      (ClightLang.Core_Callstate (Internal atomic_CAS_function)
        [Vptr b ofs; Vint expected; Vint new] Kstop)
      (ClightLang.Core_Callstate ent_atom_external [] (cas_ent_cont le)).
  Proof.
    intros le.
    destruct (marker_call_fstep2 ge atomic_CAS_function empty_env le m
      GAST.ent_atom ent_block ent_atom_external
      (Kseq cas_body_tail Kstop)) as [marker_fp Hcall].
    - reflexivity.
    - exact Hent_symbol.
    - exact Hent_fun.
    - exact (proj1 marker_external_signatures).
    - eapply fstep2_star_cons.
      + eapply ClightLang.step_internal_function.
        * apply atomic_CAS_function_entry.
        * constructor. constructor.
      + eapply fstep2_star_cons.
        * apply ClightLang.step_seq.
        * eapply fstep2_star_cons.
          -- exact Hcall.
          -- constructor.
  Qed.

  (** From the entry marker through the read and successful comparison, up
      to (but not including) the unique memory-changing assignment. *)
  Lemma atomic_CAS_ent_to_success_assign
      (ge : Clight.genv) (m : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (expected new : int)
      (Hload :
        FMemory.Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint expected)) :
    let le0 := CAS_entry_temps
      (Vptr b ofs) (Vint expected) (Vint new) in
    let le1 := PTree.set old_temp (Vint expected) le0 in
    fstep2_star ge m
      (ClightLang.Core_Returnstate Vundef (cas_ent_cont le0))
      (cas_success_assign_state le1).
  Proof.
    intros le0 le1.
    assert (Hread :
      ClightLang.eval_expr ge empty_env le0 m target_lvalue
        (Vint expected)).
    { eapply eval_target_load; eauto. apply CAS_entry_target_lookup. }
    destruct (ClightLang.eval_expr_fp_exists
      ge empty_env le0 m _ _ Hread) as [read_fp Hread_fp].
    assert (Hcmp :
      ClightLang.eval_expr ge empty_env le1 m cas_test Vtrue).
    { unfold cas_test.
      eapply eval_CAS_comparison.
      - unfold le1. apply PTree.gss.
      - unfold le1. rewrite PTree.gso by discriminate.
        apply CAS_entry_expected_lookup.
      - apply sem_CAS_eq_true. }
    destruct (ClightLang.eval_expr_fp_exists
      ge empty_env le1 m _ _ Hcmp) as [cmp_fp Hcmp_fp].
    eapply fstep2_star_cons.
    - apply ClightLang.step_returnstate.
    - cbn [set_opttemp].
      eapply fstep2_star_cons.
      + apply ClightLang.step_skip_seq.
      + eapply fstep2_star_cons.
        * apply ClightLang.step_seq.
        * eapply fstep2_star_cons.
          -- eapply ClightLang.step_set
               with (v := Vint expected) (fp := read_fp).
             ++ exact Hread.
             ++ exact Hread_fp.
          -- eapply fstep2_star_cons.
             ++ apply ClightLang.step_skip_seq.
             ++ eapply fstep2_star_cons.
                ** apply ClightLang.step_seq.
                ** eapply fstep2_star_cons.
                   --- eapply ClightLang.step_ifthenelse
                         with (v1 := Vtrue) (b := true)
                              (fp1 := cmp_fp) (fp2 := FP.emp)
                              (fp := FP.union cmp_fp FP.emp).
                       +++ exact Hcmp.
                       +++ reflexivity.
                       +++ exact Hcmp_fp.
                       +++ reflexivity.
                       +++ reflexivity.
                   --- eapply fstep2_star_cons.
                       +++ apply ClightLang.step_seq.
                       +++ constructor.
  Qed.

  Lemma atomic_CAS_success_assign
      (ge : Clight.genv) (m m' : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (expected new : int)
      (Hstore :
        FMemory.Mem.storev Mint32 m (Vptr b ofs) (Vint new) = Some m') :
    let le0 := CAS_entry_temps
      (Vptr b ofs) (Vint expected) (Vint new) in
    let le1 := PTree.set old_temp (Vint expected) le0 in
    exists fp,
      ClightLang.Fstep2 ge
        (cas_success_assign_state le1) m fp
        (cas_success_after_assign_state le1) m'.
  Proof.
    intros le0 le1.
    assert (Htarget : le1 ! target_temp = Some (Vptr b ofs)).
    { unfold le1. rewrite PTree.gso by discriminate.
      apply CAS_entry_target_lookup. }
    assert (Hnew : le1 ! new_temp = Some (Vint new)).
    { unfold le1. rewrite PTree.gso by discriminate.
      apply CAS_entry_new_lookup. }
    unfold cas_success_assign_state, cas_success_after_assign_state.
    eapply target_assignment_fstep2; eauto.
  Qed.

  Lemma atomic_CAS_success_after_assign_to_ext
      (ge : Clight.genv) (m : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (expected new : int)
      (ext_block : block)
      (Hext_symbol :
        Genv.find_symbol ge GAST.ext_atom = Some ext_block)
      (Hext_fun :
        Genv.find_funct_ptr ge ext_block = Some ext_atom_external) :
    let le0 := CAS_entry_temps
      (Vptr b ofs) (Vint expected) (Vint new) in
    let le1 := PTree.set old_temp (Vint expected) le0 in
    let le2 := PTree.set result_temp Vtrue le1 in
    fstep2_star ge m
      (cas_success_after_assign_state le1)
      (ClightLang.Core_Callstate ext_atom_external [] (cas_ext_cont le2)).
  Proof.
    intros le0 le1 le2.
    destruct (marker_call_fstep2 ge atomic_CAS_function empty_env le2 m
      GAST.ext_atom ext_block ext_atom_external
      (Kseq cas_return_statement Kstop)) as [marker_fp Hcall].
    - reflexivity.
    - exact Hext_symbol.
    - exact Hext_fun.
    - exact (proj2 marker_external_signatures).
    - eapply fstep2_star_cons.
      + apply ClightLang.step_skip_seq.
      + eapply fstep2_star_cons.
        * eapply ClightLang.step_set
            with (v := Vtrue) (fp := FP.emp).
          -- constructor.
          -- constructor.
        * eapply fstep2_star_cons.
          -- apply ClightLang.step_skip_seq.
          -- eapply fstep2_star_cons.
             ++ apply ClightLang.step_seq.
             ++ eapply fstep2_star_cons.
                ** exact Hcall.
                ** constructor.
  Qed.

  (** The failure branch performs the read and test, constructs zero, and
      reaches the exit marker without changing memory. *)
  Lemma atomic_CAS_ent_to_failure_ext
      (ge : Clight.genv) (m : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (old expected new : int)
      (ext_block : block)
      (Hneq : old <> expected)
      (Hload :
        FMemory.Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint old))
      (Hext_symbol :
        Genv.find_symbol ge GAST.ext_atom = Some ext_block)
      (Hext_fun :
        Genv.find_funct_ptr ge ext_block = Some ext_atom_external) :
    let le0 := CAS_entry_temps
      (Vptr b ofs) (Vint expected) (Vint new) in
    let le1 := PTree.set old_temp (Vint old) le0 in
    let le2 := PTree.set result_temp Vfalse le1 in
    fstep2_star ge m
      (ClightLang.Core_Returnstate Vundef (cas_ent_cont le0))
      (ClightLang.Core_Callstate ext_atom_external [] (cas_ext_cont le2)).
  Proof.
    intros le0 le1 le2.
    destruct (marker_call_fstep2 ge atomic_CAS_function empty_env le2 m
      GAST.ext_atom ext_block ext_atom_external
      (Kseq cas_return_statement Kstop)) as [marker_fp Hcall].
    - reflexivity.
    - exact Hext_symbol.
    - exact Hext_fun.
    - exact (proj2 marker_external_signatures).
    - assert (Hread :
        ClightLang.eval_expr ge empty_env le0 m target_lvalue (Vint old)).
      { eapply eval_target_load; eauto. apply CAS_entry_target_lookup. }
      destruct (ClightLang.eval_expr_fp_exists
        ge empty_env le0 m _ _ Hread) as [read_fp Hread_fp].
      assert (Hcmp :
        ClightLang.eval_expr ge empty_env le1 m cas_test Vfalse).
      { unfold cas_test.
        eapply eval_CAS_comparison.
        - unfold le1. apply PTree.gss.
        - unfold le1. rewrite PTree.gso by discriminate.
          apply CAS_entry_expected_lookup.
        - apply sem_CAS_eq_false. exact Hneq. }
      destruct (ClightLang.eval_expr_fp_exists
        ge empty_env le1 m _ _ Hcmp) as [cmp_fp Hcmp_fp].
      eapply fstep2_star_cons.
      + apply ClightLang.step_returnstate.
      + cbn [set_opttemp].
        eapply fstep2_star_cons.
        * apply ClightLang.step_skip_seq.
        * eapply fstep2_star_cons.
          -- apply ClightLang.step_seq.
          -- eapply fstep2_star_cons.
             ++ eapply ClightLang.step_set
                  with (v := Vint old) (fp := read_fp).
                ** exact Hread.
                ** exact Hread_fp.
             ++ eapply fstep2_star_cons.
                ** apply ClightLang.step_skip_seq.
                ** eapply fstep2_star_cons.
                   --- apply ClightLang.step_seq.
                   --- eapply fstep2_star_cons.
                       +++ eapply ClightLang.step_ifthenelse
                             with (v1 := Vfalse) (b := false)
                                  (fp1 := cmp_fp) (fp2 := FP.emp)
                                  (fp := FP.union cmp_fp FP.emp).
                           *** exact Hcmp.
                           *** reflexivity.
                           *** exact Hcmp_fp.
                           *** reflexivity.
                           *** reflexivity.
                       +++ eapply fstep2_star_cons.
                           *** eapply ClightLang.step_set
                                 with (v := Vfalse) (fp := FP.emp).
                               { constructor. }
                               { constructor. }
                           *** eapply fstep2_star_cons.
                               { apply ClightLang.step_skip_seq. }
                               eapply fstep2_star_cons.
                               { apply ClightLang.step_seq. }
                               eapply fstep2_star_cons.
                               { exact Hcall. }
                               constructor.
  Qed.

  Lemma atomic_CAS_ext_to_return
      (ge : Clight.genv) (m : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (expected new : int)
      (old result : int) :
    let le0 := CAS_entry_temps
      (Vptr b ofs) (Vint expected) (Vint new) in
    let le1 := PTree.set old_temp (Vint old) le0 in
    let le2 := PTree.set result_temp (Vint result) le1 in
    fstep2_star ge m
      (ClightLang.Core_Returnstate Vundef (cas_ext_cont le2))
      (ClightLang.Core_Returnstate (Vint result) Kstop).
  Proof.
    intros le0 le1 le2.
    eapply fstep2_star_cons.
    - apply ClightLang.step_returnstate.
    - cbn [set_opttemp].
      eapply fstep2_star_cons.
      + apply ClightLang.step_skip_seq.
      + eapply fstep2_star_cons.
        * eapply ClightLang.step_return_1
            with (v := Vint result) (v' := Vint result) (m' := m)
                 (fp1 := FP.emp) (fp2 := FP.emp)
                 (fp3 := FP.emp)
                 (fp := FP.union (FP.union FP.emp FP.emp) FP.emp).
          -- constructor. unfold le2. rewrite PTree.gss. reflexivity.
          -- reflexivity.
          -- reflexivity.
          -- constructor.
          -- reflexivity.
          -- reflexivity.
          -- reflexivity.
        * constructor.
  Qed.

  Lemma atomic_CAS_success_halted :
    ClightLang.halted (ClightLang.Core_Returnstate Vtrue Kstop) =
      Some Vtrue.
  Proof. reflexivity. Qed.

  Lemma atomic_CAS_failure_halted :
    ClightLang.halted (ClightLang.Core_Returnstate Vfalse Kstop) =
      Some Vfalse.
  Proof. reflexivity. Qed.

  (** The complete successful CAS path.  The two marker transitions are
      explicit boundaries; the only memory-changing local edge is [Hwrite]. *)
  Theorem atomic_CAS_success_local_macro
      (ge : Clight.genv) (m m' : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (expected new : int)
      (ent_block ext_block : block)
      (Hload :
        FMemory.Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint expected))
      (Hstore :
        FMemory.Mem.storev Mint32 m (Vptr b ofs) (Vint new) = Some m')
      (Hent_symbol :
        Genv.find_symbol ge GAST.ent_atom = Some ent_block)
      (Hent_fun :
        Genv.find_funct_ptr ge ent_block = Some ent_atom_external)
      (Hext_symbol :
        Genv.find_symbol ge GAST.ext_atom = Some ext_block)
      (Hext_fun :
        Genv.find_funct_ptr ge ext_block = Some ext_atom_external) :
    let le0 := CAS_entry_temps
      (Vptr b ofs) (Vint expected) (Vint new) in
    let le1 := PTree.set old_temp (Vint expected) le0 in
    let le2 := PTree.set result_temp Vtrue le1 in
    let ent_call :=
      ClightLang.Core_Callstate ent_atom_external [] (cas_ent_cont le0) in
    let ent_resume :=
      ClightLang.Core_Returnstate Vundef (cas_ent_cont le0) in
    let assign_state := cas_success_assign_state le1 in
    let after_assign := cas_success_after_assign_state le1 in
    let ext_call :=
      ClightLang.Core_Callstate ext_atom_external [] (cas_ext_cont le2) in
    let ext_resume :=
      ClightLang.Core_Returnstate Vundef (cas_ext_cont le2) in
    exists write_fp,
      fstep2_star ge m
        (ClightLang.Core_Callstate (Internal atomic_CAS_function)
          [Vptr b ofs; Vint expected; Vint new] Kstop) ent_call /\
      InteractionSemantics.at_external Clight_IS_2_with_markers ge ent_call =
        Some (GAST.ent_atom, GAST.ent_atom_sg, []) /\
      InteractionSemantics.after_external Clight_IS_2_with_markers
        ent_call None = Some ent_resume /\
      fstep2_star ge m ent_resume assign_state /\
      ClightLang.Fstep2 ge assign_state m write_fp after_assign m' /\
      fstep2_star ge m' after_assign ext_call /\
      InteractionSemantics.at_external Clight_IS_2_with_markers ge ext_call =
        Some (GAST.ext_atom, GAST.ext_atom_sg, []) /\
      InteractionSemantics.after_external Clight_IS_2_with_markers
        ext_call None = Some ext_resume /\
      fstep2_star ge m' ext_resume
        (ClightLang.Core_Returnstate Vtrue Kstop) /\
      ClightLang.halted (ClightLang.Core_Returnstate Vtrue Kstop) =
        Some Vtrue.
  Proof.
    intros le0 le1 le2 ent_call ent_resume assign_state after_assign
      ext_call ext_resume.
    destruct (atomic_CAS_success_assign ge m m' b ofs expected new Hstore)
      as [write_fp Hwrite].
    cbn beta in Hwrite.
    exists write_fp.
    split.
    - eapply atomic_CAS_to_ent; eauto.
    - split.
      + apply wrapper_ent_atom_builtin_is_exposed.
      + split.
        * apply wrapper_after_ent_atom.
        * split.
          -- eapply atomic_CAS_ent_to_success_assign; eauto.
          -- split.
             ++ exact Hwrite.
             ++ split.
                ** eapply atomic_CAS_success_after_assign_to_ext; eauto.
                ** split.
                   --- apply wrapper_ext_atom_builtin_is_exposed.
                   --- split.
                       +++ apply wrapper_after_ext_atom.
                       +++ split.
                           *** apply atomic_CAS_ext_to_return.
                           *** apply atomic_CAS_success_halted.
  Qed.

  (** The complete failed CAS path.  It reads and compares under the atomic
      markers but contains no memory-changing edge. *)
  Theorem atomic_CAS_failure_local_macro
      (ge : Clight.genv) (m : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (old expected new : int)
      (ent_block ext_block : block)
      (Hneq : old <> expected)
      (Hload :
        FMemory.Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint old))
      (Hent_symbol :
        Genv.find_symbol ge GAST.ent_atom = Some ent_block)
      (Hent_fun :
        Genv.find_funct_ptr ge ent_block = Some ent_atom_external)
      (Hext_symbol :
        Genv.find_symbol ge GAST.ext_atom = Some ext_block)
      (Hext_fun :
        Genv.find_funct_ptr ge ext_block = Some ext_atom_external) :
    let le0 := CAS_entry_temps
      (Vptr b ofs) (Vint expected) (Vint new) in
    let le1 := PTree.set old_temp (Vint old) le0 in
    let le2 := PTree.set result_temp Vfalse le1 in
    let ent_call :=
      ClightLang.Core_Callstate ent_atom_external [] (cas_ent_cont le0) in
    let ent_resume :=
      ClightLang.Core_Returnstate Vundef (cas_ent_cont le0) in
    let ext_call :=
      ClightLang.Core_Callstate ext_atom_external [] (cas_ext_cont le2) in
    let ext_resume :=
      ClightLang.Core_Returnstate Vundef (cas_ext_cont le2) in
    fstep2_star ge m
      (ClightLang.Core_Callstate (Internal atomic_CAS_function)
        [Vptr b ofs; Vint expected; Vint new] Kstop) ent_call /\
    InteractionSemantics.at_external Clight_IS_2_with_markers ge ent_call =
      Some (GAST.ent_atom, GAST.ent_atom_sg, []) /\
    InteractionSemantics.after_external Clight_IS_2_with_markers
      ent_call None = Some ent_resume /\
    fstep2_star ge m ent_resume ext_call /\
    InteractionSemantics.at_external Clight_IS_2_with_markers ge ext_call =
      Some (GAST.ext_atom, GAST.ext_atom_sg, []) /\
    InteractionSemantics.after_external Clight_IS_2_with_markers
      ext_call None = Some ext_resume /\
    fstep2_star ge m ext_resume
      (ClightLang.Core_Returnstate Vfalse Kstop) /\
    ClightLang.halted (ClightLang.Core_Returnstate Vfalse Kstop) =
      Some Vfalse.
  Proof.
    intros le0 le1 le2 ent_call ent_resume ext_call ext_resume.
    split.
    - eapply atomic_CAS_to_ent; eauto.
    - split.
      + apply wrapper_ent_atom_builtin_is_exposed.
      + split.
        * apply wrapper_after_ent_atom.
        * split.
          -- eapply atomic_CAS_ent_to_failure_ext; eauto.
          -- split.
             ++ apply wrapper_ext_atom_builtin_is_exposed.
             ++ split.
                ** apply wrapper_after_ext_atom.
                ** split.
                   --- apply atomic_CAS_ext_to_return.
                   --- apply atomic_CAS_failure_halted.
  Qed.

  Lemma storev_freelist_eq
      (m m' : FMemory.Mem.mem) chunk b ofs v
      (Hstore :
        FMemory.Mem.storev chunk m (Vptr b ofs) v = Some m') :
    FMemory.Mem.freelist m = FMemory.Mem.freelist m'.
  Proof.
    unfold FMemory.Mem.storev in Hstore.
    symmetry.
    eapply FMemory.Mem.store_freelist; eauto.
  Qed.

  (** Target-language successful CAS.  The middle star contains the read,
      test, conditional [Mint32] store, result construction, and exit call. *)
  Corollary atomic_CAS_success_step2_macro
      (ge : Clight.genv) (fl : MemAux.freelist)
      (gm : GMemory.gmem) (m m' : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (expected new : int)
      (ent_block ext_block : block)
      (Hembed : FMemory.embed gm fl m)
      (Hload :
        FMemory.Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint expected))
      (Hstore :
        FMemory.Mem.storev Mint32 m (Vptr b ofs) (Vint new) = Some m')
      (Hent_symbol :
        Genv.find_symbol ge GAST.ent_atom = Some ent_block)
      (Hent_fun :
        Genv.find_funct_ptr ge ent_block = Some ent_atom_external)
      (Hext_symbol :
        Genv.find_symbol ge GAST.ext_atom = Some ext_block)
      (Hext_fun :
        Genv.find_funct_ptr ge ext_block = Some ext_atom_external) :
    let le0 := CAS_entry_temps
      (Vptr b ofs) (Vint expected) (Vint new) in
    let le1 := PTree.set old_temp (Vint expected) le0 in
    let le2 := PTree.set result_temp Vtrue le1 in
    let ent_call :=
      ClightLang.Core_Callstate ent_atom_external [] (cas_ent_cont le0) in
    let ent_resume :=
      ClightLang.Core_Returnstate Vundef (cas_ent_cont le0) in
    let ext_call :=
      ClightLang.Core_Callstate ext_atom_external [] (cas_ext_cont le2) in
    let ext_resume :=
      ClightLang.Core_Returnstate Vundef (cas_ext_cont le2) in
    exists fp0 fp1 fp2,
      InteractionSemantics.star (ClightLang.step2 ge fl)
        (ClightLang.Core_Callstate (Internal atomic_CAS_function)
          [Vptr b ofs; Vint expected; Vint new] Kstop)
        gm fp0 ent_call gm /\
      InteractionSemantics.at_external Clight_IS_2_with_markers ge ent_call =
        Some (GAST.ent_atom, GAST.ent_atom_sg, []) /\
      InteractionSemantics.after_external Clight_IS_2_with_markers
        ent_call None = Some ent_resume /\
      InteractionSemantics.star (ClightLang.step2 ge fl)
        ent_resume gm fp1 ext_call (FMemory.strip m') /\
      InteractionSemantics.at_external Clight_IS_2_with_markers ge ext_call =
        Some (GAST.ext_atom, GAST.ext_atom_sg, []) /\
      InteractionSemantics.after_external Clight_IS_2_with_markers
        ext_call None = Some ext_resume /\
      InteractionSemantics.star (ClightLang.step2 ge fl)
        ext_resume (FMemory.strip m') fp2
        (ClightLang.Core_Returnstate Vtrue Kstop) (FMemory.strip m') /\
      ClightLang.halted (ClightLang.Core_Returnstate Vtrue Kstop) =
        Some Vtrue.
  Proof.
    intros le0 le1 le2 ent_call ent_resume ext_call ext_resume.
    pose proof
      (atomic_CAS_success_local_macro ge m m' b ofs expected new
        ent_block ext_block Hload Hstore Hent_symbol Hent_fun
        Hext_symbol Hext_fun) as Hmacro.
    cbn beta in Hmacro.
    destruct Hmacro as
      (write_fp & Hto_ent & Hat_ent & Hafter_ent & Hto_assign & Hwrite &
       Hafter_assign & Hat_ext & Hafter_ext & Hto_return & Hhalt).
    assert (Hembed' : FMemory.embed (FMemory.strip m') fl m').
    { inversion Hembed as [Hfl Hstrip].
      constructor.
      - rewrite <- (storev_freelist_eq m m' Mint32 b ofs
          (Vint new) Hstore). exact Hfl.
      - reflexivity. }
    destruct (fstep2_star_lift ge fl gm m _ _ Hembed Hto_ent)
      as [fp0 Hstep0].
    destruct (fstep2_star_lift ge fl gm m _ _ Hembed Hto_assign)
      as [fp_pre Hpre].
    pose proof
      (fstep2_lift ge fl gm (FMemory.strip m') m m'
        _ write_fp _ Hembed Hwrite Hembed') as Hwrite_step.
    destruct (fstep2_star_lift ge fl (FMemory.strip m') m'
      _ _ Hembed' Hafter_assign) as [fp_post Hpost].
    destruct (fstep2_star_lift ge fl (FMemory.strip m') m'
      _ _ Hembed' Hto_return) as [fp2 Hstep2].
    exists fp0, (FP.union fp_pre (FP.union write_fp fp_post)), fp2.
    split; [exact Hstep0 |].
    split; [exact Hat_ent |].
    split; [exact Hafter_ent |].
    split.
    - eapply InteractionSemantics.star_trans.
      + exact Hpre.
      + eapply InteractionSemantics.star_step.
        * exact Hwrite_step.
        * exact Hpost.
      + reflexivity.
    - split; [exact Hat_ext |].
      split; [exact Hafter_ext |].
      split; assumption.
  Qed.

  (** Target-language failed CAS.  All three internal segments preserve the
      same global memory because the conditional store is not executed. *)
  Corollary atomic_CAS_failure_step2_macro
      (ge : Clight.genv) (fl : MemAux.freelist)
      (gm : GMemory.gmem) (m : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (old expected new : int)
      (ent_block ext_block : block)
      (Hembed : FMemory.embed gm fl m)
      (Hneq : old <> expected)
      (Hload :
        FMemory.Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint old))
      (Hent_symbol :
        Genv.find_symbol ge GAST.ent_atom = Some ent_block)
      (Hent_fun :
        Genv.find_funct_ptr ge ent_block = Some ent_atom_external)
      (Hext_symbol :
        Genv.find_symbol ge GAST.ext_atom = Some ext_block)
      (Hext_fun :
        Genv.find_funct_ptr ge ext_block = Some ext_atom_external) :
    let le0 := CAS_entry_temps
      (Vptr b ofs) (Vint expected) (Vint new) in
    let le1 := PTree.set old_temp (Vint old) le0 in
    let le2 := PTree.set result_temp Vfalse le1 in
    let ent_call :=
      ClightLang.Core_Callstate ent_atom_external [] (cas_ent_cont le0) in
    let ent_resume :=
      ClightLang.Core_Returnstate Vundef (cas_ent_cont le0) in
    let ext_call :=
      ClightLang.Core_Callstate ext_atom_external [] (cas_ext_cont le2) in
    let ext_resume :=
      ClightLang.Core_Returnstate Vundef (cas_ext_cont le2) in
    exists fp0 fp1 fp2,
      InteractionSemantics.star (ClightLang.step2 ge fl)
        (ClightLang.Core_Callstate (Internal atomic_CAS_function)
          [Vptr b ofs; Vint expected; Vint new] Kstop)
        gm fp0 ent_call gm /\
      InteractionSemantics.at_external Clight_IS_2_with_markers ge ent_call =
        Some (GAST.ent_atom, GAST.ent_atom_sg, []) /\
      InteractionSemantics.after_external Clight_IS_2_with_markers
        ent_call None = Some ent_resume /\
      InteractionSemantics.star (ClightLang.step2 ge fl)
        ent_resume gm fp1 ext_call gm /\
      InteractionSemantics.at_external Clight_IS_2_with_markers ge ext_call =
        Some (GAST.ext_atom, GAST.ext_atom_sg, []) /\
      InteractionSemantics.after_external Clight_IS_2_with_markers
        ext_call None = Some ext_resume /\
      InteractionSemantics.star (ClightLang.step2 ge fl)
        ext_resume gm fp2
        (ClightLang.Core_Returnstate Vfalse Kstop) gm /\
      ClightLang.halted (ClightLang.Core_Returnstate Vfalse Kstop) =
        Some Vfalse.
  Proof.
    intros le0 le1 le2 ent_call ent_resume ext_call ext_resume.
    pose proof
      (atomic_CAS_failure_local_macro ge m b ofs old expected new
        ent_block ext_block Hneq Hload Hent_symbol Hent_fun
        Hext_symbol Hext_fun) as Hmacro.
    cbn beta in Hmacro.
    destruct Hmacro as
      (Hto_ent & Hat_ent & Hafter_ent & Hto_ext & Hat_ext &
       Hafter_ext & Hto_return & Hhalt).
    destruct (fstep2_star_lift ge fl gm m _ _ Hembed Hto_ent)
      as [fp0 Hstep0].
    destruct (fstep2_star_lift ge fl gm m _ _ Hembed Hto_ext)
      as [fp1 Hstep1].
    destruct (fstep2_star_lift ge fl gm m _ _ Hembed Hto_return)
      as [fp2 Hstep2].
    exists fp0, fp1, fp2.
    repeat split; assumption.
  Qed.

End ClightAtomicCASSteps.
