(** Local Clight paths through the concrete atomic wrappers.

    Marker entry and exit are not [ClightLang.Fstep2] transitions: they are
    handled by [GlobSemantics.Ent_Atom] and [GlobSemantics.Ext_Atom].  The
    load macro is therefore factored into three concrete [Fstep2] stars,
    separated by the two exposed marker call states. *)

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
Require Import compcert.concurrency.common.clight_val_casted.
Require Import compcert.concurrency.comp_correct.cfrontend.Cop_fp.
Require Import compcert.concurrency.comp_correct.ClightLang.

Require Import atomic_machine.clight_is2_markers.
Require Import atomic_machine.clight_atomic_wrappers.

From Stdlib Require Import List.
Import ListNotations.

Module ClightAtomicWrapperSteps.

  Import ClightAtomicWrappers.

  (** Reflexive-transitive closure of the actual footprint-indexed local
      Clight relation, specialized to paths which preserve [m].  This is the
      right closure for [atomic_load]: entering the wrapper, reading, and
      returning do not modify memory.  Footprints remain present on every
      edge and are re-accumulated by [fstep2_star_lift] below. *)
  Inductive fstep2_star (ge : Clight.genv) (m : FMemory.Mem.mem) :
      ClightLang.core -> ClightLang.core -> Prop :=
  | fstep2_star_refl c :
      fstep2_star ge m c c
  | fstep2_star_cons c1 fp c2 c3
      (Hstep : ClightLang.Fstep2 ge c1 m fp c2 m)
      (Hstar : fstep2_star ge m c2 c3) :
      fstep2_star ge m c1 c3.

  Lemma fstep2_star_trans ge m c1 c2 c3 :
    fstep2_star ge m c1 c2 ->
    fstep2_star ge m c2 c3 ->
    fstep2_star ge m c1 c3.
  Proof.
    intros H12 H23. induction H12.
    - exact H23.
    - eapply fstep2_star_cons; eauto.
  Qed.

  (** Lift a constant-[FMemory] path to the [GMemory] relation which is the
      [step] field of both [Clight_IS_2] and
      [Clight_IS_2_with_markers]. *)
  Lemma fstep2_star_lift ge fl gm m c c'
      (Hembed : FMemory.embed gm fl m) :
    fstep2_star ge m c c' ->
    exists fp,
      InteractionSemantics.star (ClightLang.step2 ge fl)
        c gm fp c' gm.
  Proof.
    assert (Hstrip : FMemory.strip m = gm).
    { inversion Hembed. assumption. }
    intros Hstar. induction Hstar.
    - exists FP.emp. constructor.
    - destruct IHHstar as [fp' IH].
      exists (FP.union fp fp').
      econstructor.
      + eapply ClightLang.Step2_intro with (m := m) (m' := m).
        * exact Hembed.
        * exact Hstep.
        * exact Hstrip.
      + exact IH.
  Qed.

  (** Lift one memory-changing local edge.  Store and successful-CAS paths
      share this bridge between [Fstep2] and the target [step2] relation. *)
  Lemma fstep2_lift
      (ge : Clight.genv) (fl : MemAux.freelist)
      (gm gm' : GMemory.gmem) (m m' : FMemory.Mem.mem)
      c fp c'
      (Hembed : FMemory.embed gm fl m)
      (Hstep : ClightLang.Fstep2 ge c m fp c' m')
      (Hembed' : FMemory.embed gm' fl m') :
    ClightLang.step2 ge fl c gm fp c' gm'.
  Proof.
    assert (Hstrip : FMemory.strip m' = gm').
    { inversion Hembed'. assumption. }
    eapply ClightLang.Step2_intro with (m := m) (m' := m').
    - exact Hembed.
    - exact Hstep.
    - exact Hstrip.
  Qed.

  (** The unique [Mint32] assignment edge used by both the store wrapper and
      the successful branch of the CAS wrapper. *)
  Lemma target_assignment_fstep2
      (ge : Clight.genv) (f : function) (k : cont)
      (le : temp_env) (m m' : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (n : int)
      (Htarget : le ! target_temp = Some (Vptr b ofs))
      (Hnew : le ! new_temp = Some (Vint n))
      (Hstore :
        FMemory.Mem.storev Mint32 m (Vptr b ofs) (Vint n) = Some m') :
    exists fp,
      ClightLang.Fstep2 ge
        (ClightLang.Core_State f (Sassign target_lvalue new_expr)
          k empty_env le) m fp
        (ClightLang.Core_State f Sskip k empty_env le) m'.
  Proof.
    assert (Hlv :
      ClightLang.eval_lvalue ge empty_env le m target_lvalue b ofs).
    { apply eval_target_lvalue. exact Htarget. }
    assert (Hex :
      ClightLang.eval_expr ge empty_env le m new_expr (Vint n)).
    { constructor. exact Hnew. }
    assert (Hcast :
      FCop.sem_cast (Vint n) (typeof new_expr) (typeof target_lvalue) m =
        Some (Vint n)) by reflexivity.
    assert (Hassign :
      ClightLang.assign_loc ge (typeof target_lvalue) m b ofs
        (Vint n) m').
    { apply assign_target_store. exact Hstore. }
    destruct (ClightLang.eval_lvalue_fp_exists
      ge empty_env le m _ _ _ Hlv) as [fp1 Hfp1].
    destruct (ClightLang.eval_expr_fp_exists
      ge empty_env le m _ _ Hex) as [fp2 Hfp2].
    destruct (sem_cast_sem_cast_fp _ _ _ _ _ Hcast) as [fp3 Hfp3].
    destruct (ClightLang.assign_loc_fp_exists
      ge (typeof target_lvalue) m b ofs (Vint n) m' Hassign)
      as [fp4 Hfp4].
    exists (FP.union (FP.union (FP.union fp1 fp2) fp3) fp4).
    eapply ClightLang.step_assign
      with (loc := b) (ofs := ofs) (v2 := Vint n) (v := Vint n)
           (m' := m') (fp1 := fp1) (fp2 := fp2)
           (fp3 := fp3) (fp4 := fp4); eauto.
  Qed.

  Definition load_exit_tail : statement :=
    Ssequence exit_atomic (Sreturn (Some old_expr)).

  Definition load_body_tail : statement :=
    Ssequence (Sset old_temp target_lvalue) load_exit_tail.

  Definition load_return_statement : statement :=
    Sreturn (Some old_expr).

  Definition load_ent_cont (le : temp_env) : cont :=
    Kcall None atomic_load_function empty_env le
      (Kseq load_body_tail Kstop).

  Definition load_ext_cont (le : temp_env) : cont :=
    Kcall None atomic_load_function empty_env le
      (Kseq load_return_statement Kstop).

  (** A successful defined [Mint32] read is a valid result for the canonical
      [int] load declaration, on both pointer-width configurations.  On a
      64-bit target [Mem.load_type] rules out pointers; on a 32-bit target
      CASCompCert's Clight cast semantics deliberately preserves a pointer
      through an [int]-to-[int] cast. *)
  Lemma defined_Mint32_load_self_cast m b ofs v
      (Hload : FMemory.Mem.loadv Mint32 m (Vptr b ofs) = Some v)
      (Hdefined : clight_val_casted.vals_defined [v] = true) :
    FCop.sem_cast v tint tint m = Some v.
  Proof.
    pose proof (FMemory.Mem.load_type _ _ _ _ _ Hload) as Htype.
    destruct v; cbn in Hdefined, Htype |- *; try discriminate;
      try contradiction.
    all: destruct Archi.ptr64 eqn:Hptr; cbn in Htype |- *;
      try contradiction; reflexivity.
  Qed.

  Lemma defined_Mint32_load_has_rettype m b ofs v
      (Hload : FMemory.Mem.loadv Mint32 m (Vptr b ofs) = Some v)
      (Hdefined : clight_val_casted.vals_defined [v] = true) :
    clight_val_casted.val_has_rettype_func v
      atomic_load_signature.(sig_res) = true.
  Proof.
    pose proof (FMemory.Mem.load_type _ _ _ _ _ Hload) as Htype.
    destruct v; cbn in Hdefined, Htype |- *; try discriminate;
      try contradiction.
    all: destruct Archi.ptr64 eqn:Hptr; cbn in Htype |- *;
      try contradiction; reflexivity.
  Qed.

  (** Calling a globally declared marker is an ordinary Clight call step up
      to the external [Core_Callstate]. *)
  Lemma marker_call_fstep2
      (ge : Clight.genv) (f : function) (e : env) (le : temp_env)
      (m : FMemory.Mem.mem) (id : ident) (b : block) (fd : fundef)
      (k : cont)
      (Hlocal : e ! id = None)
      (Hsymbol : Genv.find_symbol ge id = Some b)
      (Hfun : Genv.find_funct_ptr ge b = Some fd)
      (Htype : type_of_fundef fd = marker_type) :
    exists fp,
      ClightLang.Fstep2 ge
        (ClightLang.Core_State f (marker_call id) k e le) m fp
        (ClightLang.Core_Callstate fd [] (Kcall None f e le k)) m.
  Proof.
    assert (Hlv :
      ClightLang.eval_lvalue ge e le m (Evar id marker_type)
        b Ptrofs.zero).
    { apply ClightLang.eval_Evar_global; assumption. }
    assert (Hderef :
      ClightLang.deref_loc marker_type m b Ptrofs.zero
        (Vptr b Ptrofs.zero)).
    { apply ClightLang.deref_loc_reference. reflexivity. }
    assert (Hex :
      ClightLang.eval_expr ge e le m (Evar id marker_type)
        (Vptr b Ptrofs.zero)).
    { eapply ClightLang.eval_Elvalue; eauto. }
    destruct (ClightLang.eval_expr_fp_exists ge e le m _ _ Hex)
      as [fp Hfp].
    exists (FP.union fp FP.emp).
    eapply ClightLang.step_call
      with (tyargs := []) (tyres := tvoid) (cconv := cc_default)
           (vf := Vptr b Ptrofs.zero) (vargs := []) (fd := fd)
           (fp1 := fp) (fp2 := FP.emp).
    - reflexivity.
    - exact Hex.
    - constructor.
    - unfold Genv.find_funct. simpl. exact Hfun.
    - exact Htype.
    - exact Hfp.
    - constructor.
    - reflexivity.
  Qed.

  Lemma atomic_load_to_ent
      (ge : Clight.genv) (m : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (ent_block : block)
      (Hent_symbol :
        Genv.find_symbol ge GAST.ent_atom = Some ent_block)
      (Hent_fun :
        Genv.find_funct_ptr ge ent_block = Some ent_atom_external) :
    let le := load_entry_temps (Vptr b ofs) in
    fstep2_star ge m
      (ClightLang.Core_Callstate (Internal atomic_load_function)
        [Vptr b ofs] Kstop)
      (ClightLang.Core_Callstate ent_atom_external [] (load_ent_cont le)).
  Proof.
    intros le.
    destruct (marker_call_fstep2 ge atomic_load_function empty_env le m
      GAST.ent_atom ent_block ent_atom_external
      (Kseq load_body_tail Kstop)) as [marker_fp Hcall].
    - reflexivity.
    - exact Hent_symbol.
    - exact Hent_fun.
    - exact (proj1 marker_external_signatures).
    eapply fstep2_star_cons.
    - eapply ClightLang.step_internal_function.
      + apply atomic_load_function_entry.
      + constructor. constructor.
    - eapply fstep2_star_cons.
      + apply ClightLang.step_seq.
      + eapply fstep2_star_cons.
        * exact Hcall.
        * constructor.
  Qed.

  Lemma atomic_load_ent_to_ext
      (ge : Clight.genv) (m : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (v : val) (ext_block : block)
      (Hload : FMemory.Mem.loadv Mint32 m (Vptr b ofs) = Some v)
      (Hext_symbol :
        Genv.find_symbol ge GAST.ext_atom = Some ext_block)
      (Hext_fun :
        Genv.find_funct_ptr ge ext_block = Some ext_atom_external) :
    let le0 := load_entry_temps (Vptr b ofs) in
    let le1 := PTree.set old_temp v le0 in
    fstep2_star ge m
      (ClightLang.Core_Returnstate Vundef (load_ent_cont le0))
      (ClightLang.Core_Callstate ext_atom_external [] (load_ext_cont le1)).
  Proof.
    intros le0 le1.
    destruct (marker_call_fstep2 ge atomic_load_function empty_env le1 m
      GAST.ext_atom ext_block ext_atom_external
      (Kseq load_return_statement Kstop)) as [marker_fp Hcall].
    - reflexivity.
    - exact Hext_symbol.
    - exact Hext_fun.
    - exact (proj2 marker_external_signatures).
    assert (Heval :
      ClightLang.eval_expr ge empty_env le0 m target_lvalue v).
    { eapply eval_target_load; eauto. unfold le0, load_entry_temps.
      rewrite PTree.gss. reflexivity. }
    destruct (ClightLang.eval_expr_fp_exists ge empty_env le0 m _ _ Heval)
      as [read_fp Hread_fp].
    eapply fstep2_star_cons.
    - apply ClightLang.step_returnstate.
    - cbn [set_opttemp].
      eapply fstep2_star_cons.
      + apply ClightLang.step_skip_seq.
      + eapply fstep2_star_cons.
        * apply ClightLang.step_seq.
        * eapply fstep2_star_cons.
          -- eapply ClightLang.step_set
               with (v := v) (fp := read_fp).
             ++ exact Heval.
             ++ exact Hread_fp.
          -- eapply fstep2_star_cons.
             ++ apply ClightLang.step_skip_seq.
             ++ eapply fstep2_star_cons.
                ** apply ClightLang.step_seq.
                ** eapply fstep2_star_cons.
                   --- exact Hcall.
                   --- constructor.
  Qed.

  Lemma atomic_load_ext_to_return
      (ge : Clight.genv) (m : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (v : val)
      (Hload : FMemory.Mem.loadv Mint32 m (Vptr b ofs) = Some v)
      (Hdefined : clight_val_casted.vals_defined [v] = true) :
    let le0 := load_entry_temps (Vptr b ofs) in
    let le1 := PTree.set old_temp v le0 in
    fstep2_star ge m
      (ClightLang.Core_Returnstate Vundef (load_ext_cont le1))
      (ClightLang.Core_Returnstate v Kstop).
  Proof.
    intros le0 le1.
    pose proof
      (defined_Mint32_load_self_cast m b ofs v Hload Hdefined) as Hcast.
    destruct (sem_cast_sem_cast_fp _ _ _ _ _ Hcast)
      as [cast_fp Hcast_fp].
    eapply fstep2_star_cons.
    - apply ClightLang.step_returnstate.
    - cbn [set_opttemp].
      eapply fstep2_star_cons.
      + apply ClightLang.step_skip_seq.
      + eapply fstep2_star_cons.
        * eapply ClightLang.step_return_1
            with (v := v) (v' := v) (m' := m)
                 (fp1 := FP.emp) (fp2 := cast_fp)
                 (fp3 := FP.emp)
                 (fp := FP.union (FP.union FP.emp cast_fp) FP.emp).
          -- constructor. unfold le1. rewrite PTree.gss. reflexivity.
          -- exact Hcast.
          -- reflexivity.
          -- constructor.
          -- exact Hcast_fp.
          -- reflexivity.
          -- reflexivity.
        * constructor.
  Qed.

  (** A complete local load macro, with the two non-local marker transitions
      stated explicitly as [at_external]/[after_external] boundaries. *)
  Theorem atomic_load_local_macro
      (ge : Clight.genv) (m : FMemory.Mem.mem)
      (b : block) (ofs : ptrofs) (v : val)
      (ent_block ext_block : block)
      (Hload : FMemory.Mem.loadv Mint32 m (Vptr b ofs) = Some v)
      (Hdefined : clight_val_casted.vals_defined [v] = true)
      (Hent_symbol :
        Genv.find_symbol ge GAST.ent_atom = Some ent_block)
      (Hent_fun :
        Genv.find_funct_ptr ge ent_block = Some ent_atom_external)
      (Hext_symbol :
        Genv.find_symbol ge GAST.ext_atom = Some ext_block)
      (Hext_fun :
        Genv.find_funct_ptr ge ext_block = Some ext_atom_external) :
    let le0 := load_entry_temps (Vptr b ofs) in
    let le1 := PTree.set old_temp v le0 in
    let ent_call :=
      ClightLang.Core_Callstate ent_atom_external [] (load_ent_cont le0) in
    let ent_resume :=
      ClightLang.Core_Returnstate Vundef (load_ent_cont le0) in
    let ext_call :=
      ClightLang.Core_Callstate ext_atom_external [] (load_ext_cont le1) in
    let ext_resume :=
      ClightLang.Core_Returnstate Vundef (load_ext_cont le1) in
    fstep2_star ge m
      (ClightLang.Core_Callstate (Internal atomic_load_function)
        [Vptr b ofs] Kstop) ent_call /\
    InteractionSemantics.at_external Clight_IS_2_with_markers ge ent_call =
      Some (GAST.ent_atom, GAST.ent_atom_sg, []) /\
    InteractionSemantics.after_external Clight_IS_2_with_markers ent_call None =
      Some ent_resume /\
    fstep2_star ge m ent_resume ext_call /\
    InteractionSemantics.at_external Clight_IS_2_with_markers ge ext_call =
      Some (GAST.ext_atom, GAST.ext_atom_sg, []) /\
    InteractionSemantics.after_external Clight_IS_2_with_markers ext_call None =
      Some ext_resume /\
    fstep2_star ge m ext_resume
      (ClightLang.Core_Returnstate v Kstop).
  Proof.
    intros le0 le1 ent_call ent_resume ext_call ext_resume.
    split.
    - eapply atomic_load_to_ent; eauto.
    - split.
      + apply wrapper_ent_atom_builtin_is_exposed.
      + split.
        * apply wrapper_after_ent_atom.
        * split.
          -- eapply atomic_load_ent_to_ext; eauto.
          -- split.
             ++ apply wrapper_ext_atom_builtin_is_exposed.
             ++ split.
                ** apply wrapper_after_ext_atom.
                ** eapply atomic_load_ext_to_return; eauto.
  Qed.

  (** The same macro stated over the actual target-language internal-step
      relation.  The marker calls remain explicit because they are consumed
      by the global [Ent_Atom]/[Ext_Atom] rules, not by language [step]. *)
  Corollary atomic_load_step2_macro
      (ge : Clight.genv) (fl : MemAux.freelist) (gm : GMemory.gmem)
      (m : FMemory.Mem.mem) (b : block) (ofs : ptrofs) (v : val)
      (ent_block ext_block : block)
      (Hembed : FMemory.embed gm fl m)
      (Hload : FMemory.Mem.loadv Mint32 m (Vptr b ofs) = Some v)
      (Hdefined : clight_val_casted.vals_defined [v] = true)
      (Hent_symbol :
        Genv.find_symbol ge GAST.ent_atom = Some ent_block)
      (Hent_fun :
        Genv.find_funct_ptr ge ent_block = Some ent_atom_external)
      (Hext_symbol :
        Genv.find_symbol ge GAST.ext_atom = Some ext_block)
      (Hext_fun :
        Genv.find_funct_ptr ge ext_block = Some ext_atom_external) :
    let le0 := load_entry_temps (Vptr b ofs) in
    let le1 := PTree.set old_temp v le0 in
    let ent_call :=
      ClightLang.Core_Callstate ent_atom_external [] (load_ent_cont le0) in
    let ent_resume :=
      ClightLang.Core_Returnstate Vundef (load_ent_cont le0) in
    let ext_call :=
      ClightLang.Core_Callstate ext_atom_external [] (load_ext_cont le1) in
    let ext_resume :=
      ClightLang.Core_Returnstate Vundef (load_ext_cont le1) in
    exists fp0 fp1 fp2,
      InteractionSemantics.star (ClightLang.step2 ge fl)
        (ClightLang.Core_Callstate (Internal atomic_load_function)
          [Vptr b ofs] Kstop) gm fp0 ent_call gm /\
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
        (ClightLang.Core_Returnstate v Kstop) gm.
  Proof.
    intros le0 le1 ent_call ent_resume ext_call ext_resume.
    pose proof
      (atomic_load_local_macro ge m b ofs v ent_block ext_block Hload
        Hdefined Hent_symbol Hent_fun Hext_symbol Hext_fun)
      as Hmacro.
    cbn beta in Hmacro.
    destruct Hmacro as
      (Hto_ent & Hat_ent & Hafter_ent & Hto_ext & Hat_ext &
       Hafter_ext & Hto_return).
    destruct (fstep2_star_lift ge fl gm m _ _ Hembed Hto_ent)
      as [fp0 Hstep0].
    destruct (fstep2_star_lift ge fl gm m _ _ Hembed Hto_ext)
      as [fp1 Hstep1].
    destruct (fstep2_star_lift ge fl gm m _ _ Hembed Hto_return)
      as [fp2 Hstep2].
    exists fp0, fp1, fp2.
    repeat split; assumption.
  Qed.

End ClightAtomicWrapperSteps.
