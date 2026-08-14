(** Local Clight paths through the concrete [atomic_store] wrapper. *)

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Values.
Require Import compcert.cfrontend.Ctypes.
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

Module ClightAtomicStoreSteps.

  Import ClightAtomicWrappers.
  Import ClightAtomicWrapperSteps.

  Definition store_exit_tail : statement :=
    Ssequence exit_atomic
      (Sreturn (Some (Econst_int Int.zero tint))).

  Definition store_body_tail : statement :=
    Ssequence (Sassign target_lvalue new_expr) store_exit_tail.

  Definition store_return_statement : statement :=
    Sreturn (Some (Econst_int Int.zero tint)).

  Definition store_ent_cont (le : temp_env) : cont :=
    Kcall None atomic_store_function empty_env le
      (Kseq store_body_tail Kstop).

  Definition store_ext_cont (le : temp_env) : cont :=
    Kcall None atomic_store_function empty_env le
      (Kseq store_return_statement Kstop).

  Definition store_assign_state (le : temp_env) : ClightLang.core :=
    ClightLang.Core_State atomic_store_function
      (Sassign target_lvalue new_expr)
      (Kseq store_exit_tail Kstop) empty_env le.

  Definition store_after_assign_state (le : temp_env) : ClightLang.core :=
    ClightLang.Core_State atomic_store_function Sskip
      (Kseq store_exit_tail Kstop) empty_env le.

  Lemma atomic_store_to_ent
      (ge : Clight.genv) (m : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (n : int) (ent_block : block)
      (Hent_symbol :
        Genv.find_symbol ge GAST.ent_atom = Some ent_block)
      (Hent_fun :
        Genv.find_funct_ptr ge ent_block = Some ent_atom_external) :
    let le := store_entry_temps (Vptr b ofs) (Vint n) in
    fstep2_star ge m
      (ClightLang.Core_Callstate (Internal atomic_store_function)
        [Vptr b ofs; Vint n] Kstop)
      (ClightLang.Core_Callstate ent_atom_external [] (store_ent_cont le)).
  Proof.
    intros le.
    destruct (marker_call_fstep2 ge atomic_store_function empty_env le m
      GAST.ent_atom ent_block ent_atom_external
      (Kseq store_body_tail Kstop)) as [marker_fp Hcall].
    - reflexivity.
    - exact Hent_symbol.
    - exact Hent_fun.
    - exact (proj1 marker_external_signatures).
    eapply fstep2_star_cons.
    - eapply ClightLang.step_internal_function.
      + apply atomic_store_function_entry.
      + constructor. constructor.
    - eapply fstep2_star_cons.
      + apply ClightLang.step_seq.
      + eapply fstep2_star_cons.
        * exact Hcall.
        * constructor.
  Qed.

  Lemma atomic_store_ent_to_assign
      (ge : Clight.genv) (m : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (n : int) :
    let le := store_entry_temps (Vptr b ofs) (Vint n) in
    fstep2_star ge m
      (ClightLang.Core_Returnstate Vundef (store_ent_cont le))
      (store_assign_state le).
  Proof.
    intros le.
    eapply fstep2_star_cons.
    - apply ClightLang.step_returnstate.
    - cbn [set_opttemp].
      eapply fstep2_star_cons.
      + apply ClightLang.step_skip_seq.
      + eapply fstep2_star_cons.
        * apply ClightLang.step_seq.
        * constructor.
  Qed.

  Lemma atomic_store_assign
      (ge : Clight.genv) (m m' : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (n : int)
      (Hstore :
        FMemory.Mem.storev Mint32 m (Vptr b ofs) (Vint n) = Some m') :
    let le := store_entry_temps (Vptr b ofs) (Vint n) in
    exists fp,
      ClightLang.Fstep2 ge
        (store_assign_state le) m fp (store_after_assign_state le) m'.
  Proof.
    intros le.
    assert (Htarget : le ! target_temp = Some (Vptr b ofs)).
    { unfold le, store_entry_temps.
      rewrite PTree.gso; [apply PTree.gss | discriminate]. }
    assert (Hnew : le ! new_temp = Some (Vint n)).
    { unfold le, store_entry_temps. apply PTree.gss. }
    unfold store_assign_state, store_after_assign_state.
    eapply target_assignment_fstep2; eauto.
  Qed.

  Lemma atomic_store_after_assign_to_ext
      (ge : Clight.genv) (m : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (n : int) (ext_block : block)
      (Hext_symbol :
        Genv.find_symbol ge GAST.ext_atom = Some ext_block)
      (Hext_fun :
        Genv.find_funct_ptr ge ext_block = Some ext_atom_external) :
    let le := store_entry_temps (Vptr b ofs) (Vint n) in
    fstep2_star ge m
      (store_after_assign_state le)
      (ClightLang.Core_Callstate ext_atom_external [] (store_ext_cont le)).
  Proof.
    intros le.
    destruct (marker_call_fstep2 ge atomic_store_function empty_env le m
      GAST.ext_atom ext_block ext_atom_external
      (Kseq store_return_statement Kstop)) as [marker_fp Hcall].
    - reflexivity.
    - exact Hext_symbol.
    - exact Hext_fun.
    - exact (proj2 marker_external_signatures).
    eapply fstep2_star_cons.
    - apply ClightLang.step_skip_seq.
    - eapply fstep2_star_cons.
      + apply ClightLang.step_seq.
      + eapply fstep2_star_cons.
        * exact Hcall.
        * constructor.
  Qed.

  Lemma atomic_store_ext_to_return
      (ge : Clight.genv) (m : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (n : int) :
    let le := store_entry_temps (Vptr b ofs) (Vint n) in
    fstep2_star ge m
      (ClightLang.Core_Returnstate Vundef (store_ext_cont le))
      (ClightLang.Core_Returnstate Vzero Kstop).
  Proof.
    intros le.
    eapply fstep2_star_cons.
    - apply ClightLang.step_returnstate.
    - cbn [set_opttemp].
      eapply fstep2_star_cons.
      + apply ClightLang.step_skip_seq.
      + eapply fstep2_star_cons.
        * eapply ClightLang.step_return_1
            with (v := Vzero) (v' := Vzero) (m' := m)
                 (fp1 := FP.emp) (fp2 := FP.emp) (fp3 := FP.emp)
                 (fp := FP.union (FP.union FP.emp FP.emp) FP.emp).
          -- constructor.
          -- reflexivity.
          -- reflexivity.
          -- constructor.
          -- reflexivity.
          -- reflexivity.
          -- reflexivity.
        * constructor.
  Qed.

  Lemma atomic_store_return_halted :
    ClightLang.halted (ClightLang.Core_Returnstate Vzero Kstop) =
      Some Vzero.
  Proof. reflexivity. Qed.

  (** A complete local store macro.  The write edge is isolated because it
      changes footprint memory from [m] to [m']; all other segments preserve
      their respective footprint memories. *)
  Theorem atomic_store_local_macro
      (ge : Clight.genv) (m m' : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (n : int)
      (ent_block ext_block : block)
      (Hstore :
        FMemory.Mem.storev Mint32 m (Vptr b ofs) (Vint n) = Some m')
      (Hent_symbol :
        Genv.find_symbol ge GAST.ent_atom = Some ent_block)
      (Hent_fun :
        Genv.find_funct_ptr ge ent_block = Some ent_atom_external)
      (Hext_symbol :
        Genv.find_symbol ge GAST.ext_atom = Some ext_block)
      (Hext_fun :
        Genv.find_funct_ptr ge ext_block = Some ext_atom_external) :
    let le := store_entry_temps (Vptr b ofs) (Vint n) in
    let ent_call :=
      ClightLang.Core_Callstate ent_atom_external [] (store_ent_cont le) in
    let ent_resume :=
      ClightLang.Core_Returnstate Vundef (store_ent_cont le) in
    let assign_state := store_assign_state le in
    let after_assign := store_after_assign_state le in
    let ext_call :=
      ClightLang.Core_Callstate ext_atom_external [] (store_ext_cont le) in
    let ext_resume :=
      ClightLang.Core_Returnstate Vundef (store_ext_cont le) in
    exists write_fp,
      fstep2_star ge m
        (ClightLang.Core_Callstate (Internal atomic_store_function)
          [Vptr b ofs; Vint n] Kstop) ent_call /\
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
        (ClightLang.Core_Returnstate Vzero Kstop) /\
      ClightLang.halted (ClightLang.Core_Returnstate Vzero Kstop) =
        Some Vzero.
  Proof.
    intros le ent_call ent_resume assign_state after_assign ext_call ext_resume.
    destruct (atomic_store_assign ge m m' b ofs n Hstore)
      as [write_fp Hwrite].
    cbn beta in Hwrite.
    exists write_fp.
    split.
    - eapply atomic_store_to_ent; eauto.
    - split.
      + apply wrapper_ent_atom_builtin_is_exposed.
      + split.
        * apply wrapper_after_ent_atom.
        * split.
          -- apply atomic_store_ent_to_assign.
          -- split.
             ++ exact Hwrite.
             ++ split.
                ** eapply atomic_store_after_assign_to_ext; eauto.
                ** split.
                   --- apply wrapper_ext_atom_builtin_is_exposed.
                   --- split.
                       +++ apply wrapper_after_ext_atom.
                       +++ split.
                           *** apply atomic_store_ext_to_return.
                           *** apply atomic_store_return_halted.
  Qed.

  (** The target-language form of the store macro.  The second internal star
      contains the unique memory-changing [Sassign] edge. *)
  Corollary atomic_store_step2_macro
      (ge : Clight.genv) (fl : MemAux.freelist)
      (gm gm' : GMemory.gmem) (m m' : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (n : int)
      (ent_block ext_block : block)
      (Hembed : FMemory.embed gm fl m)
      (Hembed' : FMemory.embed gm' fl m')
      (Hstore :
        FMemory.Mem.storev Mint32 m (Vptr b ofs) (Vint n) = Some m')
      (Hent_symbol :
        Genv.find_symbol ge GAST.ent_atom = Some ent_block)
      (Hent_fun :
        Genv.find_funct_ptr ge ent_block = Some ent_atom_external)
      (Hext_symbol :
        Genv.find_symbol ge GAST.ext_atom = Some ext_block)
      (Hext_fun :
        Genv.find_funct_ptr ge ext_block = Some ext_atom_external) :
    let le := store_entry_temps (Vptr b ofs) (Vint n) in
    let ent_call :=
      ClightLang.Core_Callstate ent_atom_external [] (store_ent_cont le) in
    let ent_resume :=
      ClightLang.Core_Returnstate Vundef (store_ent_cont le) in
    let ext_call :=
      ClightLang.Core_Callstate ext_atom_external [] (store_ext_cont le) in
    let ext_resume :=
      ClightLang.Core_Returnstate Vundef (store_ext_cont le) in
    exists fp0 fp1 fp2,
      InteractionSemantics.star (ClightLang.step2 ge fl)
        (ClightLang.Core_Callstate (Internal atomic_store_function)
          [Vptr b ofs; Vint n] Kstop) gm fp0 ent_call gm /\
      InteractionSemantics.at_external Clight_IS_2_with_markers ge ent_call =
        Some (GAST.ent_atom, GAST.ent_atom_sg, []) /\
      InteractionSemantics.after_external Clight_IS_2_with_markers
        ent_call None = Some ent_resume /\
      InteractionSemantics.star (ClightLang.step2 ge fl)
        ent_resume gm fp1 ext_call gm' /\
      InteractionSemantics.at_external Clight_IS_2_with_markers ge ext_call =
        Some (GAST.ext_atom, GAST.ext_atom_sg, []) /\
      InteractionSemantics.after_external Clight_IS_2_with_markers
        ext_call None = Some ext_resume /\
      InteractionSemantics.star (ClightLang.step2 ge fl)
        ext_resume gm' fp2
        (ClightLang.Core_Returnstate Vzero Kstop) gm' /\
      ClightLang.halted (ClightLang.Core_Returnstate Vzero Kstop) =
        Some Vzero.
  Proof.
    intros le ent_call ent_resume ext_call ext_resume.
    pose proof
      (atomic_store_local_macro ge m m' b ofs n ent_block ext_block Hstore
        Hent_symbol Hent_fun Hext_symbol Hext_fun)
      as Hmacro.
    cbn beta in Hmacro.
    destruct Hmacro as
      (write_fp & Hto_ent & Hat_ent & Hafter_ent & Hto_assign & Hwrite &
       Hafter_assign & Hat_ext & Hafter_ext & Hto_return & Hhalt).
    destruct (fstep2_star_lift ge fl gm m _ _ Hembed Hto_ent)
      as [fp0 Hstep0].
    destruct (fstep2_star_lift ge fl gm m _ _ Hembed Hto_assign)
      as [fp_pre Hpre].
    pose proof
      (fstep2_lift ge fl gm gm' m m' _ write_fp _
        Hembed Hwrite Hembed') as Hwrite_step.
    destruct (fstep2_star_lift ge fl gm' m' _ _ Hembed' Hafter_assign)
      as [fp_post Hpost].
    destruct (fstep2_star_lift ge fl gm' m' _ _ Hembed' Hto_return)
      as [fp2 Hstep2].
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

End ClightAtomicStoreSteps.
