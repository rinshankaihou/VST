(** Static source-syntax restriction used by the Clight atomic refinement.

    CASCompCert's [ClightLang.assign_loc] contains only its ordinary
    [assign_loc_value] constructor.  The VST event semantics used by the
    atomic machine also contains copy and bit-field assignment constructors.

    Rather than defining a second atomic-machine step relation, this file
    characterizes the Clight assignment syntax for which every actual
    [assign_locT] derivation must use [assign_locT_value].  Executions continue
    to use the unchanged [Clight_language] and the ordinary [at_step]. *)

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.cfrontend.Clight.

From Stdlib Require Import List.
From Stdlib Require Import Program.Equality.

Require Import VST.sepcomp.event_semantics.
Set Warnings "-custom-entry-overridden".
Require Import VST.veric.Clight_evsem.
Set Warnings "custom-entry-overridden".

Require Import compcert.concurrency.comp_correct.ClightLang.
Require Import atomic_machine.atomic_machine.
Require Import atomic_machine.clight_at_mach.

Import Address Values.
Import ListNotations.

(** A syntactically admissible assignment lvalue must evaluate to a complete
    object, not to a bit-field designation.  Variables and dereferences are
    always [Full].  A field is admitted only when the statically computed
    composite layout says that this particular member is [Full]. *)
Inductive clight_full_lvalue_syntax
    (ce : Ctypes.composite_env) : Clight.expr -> Prop :=
| clight_full_lvalue_var : forall id ty,
    clight_full_lvalue_syntax ce (Clight.Evar id ty)
| clight_full_lvalue_deref : forall a ty,
    clight_full_lvalue_syntax ce (Clight.Ederef a ty)
| clight_full_lvalue_field_struct :
    forall a field ty id attr co delta,
      Clight.typeof a = Ctypes.Tstruct id attr ->
      Maps.PTree.get id ce = Some co ->
      Ctypes.field_offset ce field (Ctypes.co_members co) =
        Errors.OK (delta, Ctypes.Full) ->
      clight_full_lvalue_syntax ce (Clight.Efield a field ty)
| clight_full_lvalue_field_union :
    forall a field ty id attr co delta,
      Clight.typeof a = Ctypes.Tunion id attr ->
      Maps.PTree.get id ce = Some co ->
      Ctypes.union_field_offset ce field (Ctypes.co_members co) =
        Errors.OK (delta, Ctypes.Full) ->
      clight_full_lvalue_syntax ce (Clight.Efield a field ty).

(** [By_value] rules out structure/union block copies.  The independent
    [clight_full_lvalue_syntax] premise rules out bit-field stores, whose
    integer type also has [By_value] access mode. *)
Definition clight_assign_loc_value_lhs
    (ce : Ctypes.composite_env) (lhs : Clight.expr) : Prop :=
  clight_full_lvalue_syntax ce lhs /\
  exists chunk,
    Ctypes.access_mode (Clight.typeof lhs) = Ctypes.By_value chunk.

(** Static traversal of all statements in a function body. *)
Fixpoint clight_statement_assign_loc_value_only
    (ce : Ctypes.composite_env) (s : Clight.statement) : Prop :=
  match s with
  | Clight.Sassign lhs _ => clight_assign_loc_value_lhs ce lhs
  | Clight.Ssequence s1 s2
  | Clight.Sloop s1 s2 =>
      clight_statement_assign_loc_value_only ce s1 /\
      clight_statement_assign_loc_value_only ce s2
  | Clight.Sifthenelse _ s1 s2 =>
      clight_statement_assign_loc_value_only ce s1 /\
      clight_statement_assign_loc_value_only ce s2
  | Clight.Sswitch _ cases =>
      clight_labeled_assign_loc_value_only ce cases
  | Clight.Slabel _ body =>
      clight_statement_assign_loc_value_only ce body
  | _ => True
  end
with clight_labeled_assign_loc_value_only
    (ce : Ctypes.composite_env) (cases : Clight.labeled_statements) : Prop :=
  match cases with
  | Clight.LSnil => True
  | Clight.LScons _ body rest =>
      clight_statement_assign_loc_value_only ce body /\
      clight_labeled_assign_loc_value_only ce rest
  end.

Definition clight_function_assign_loc_value_only
    (ce : Ctypes.composite_env) (f : Clight.function) : Prop :=
  clight_statement_assign_loc_value_only ce (Clight.fn_body f).

Definition clight_globdef_assign_loc_value_only
    (ce : Ctypes.composite_env)
    (gd : AST.globdef Clight.fundef Ctypes.type) : Prop :=
  match gd with
  | AST.Gfun (Ctypes.Internal f) =>
      clight_function_assign_loc_value_only ce f
  | _ => True
  end.

(** A checkable, program-level form of the restriction.  Connecting this
    predicate to an arbitrary running source configuration additionally needs
    the usual initialization/core-provenance invariant. *)
Definition clight_comp_unit_assign_loc_value_only
    (cu : ClightLang.clight_comp_unit) : Prop :=
  forall id gd,
    In (id, gd) (ClightLang.cu_defs cu) ->
    clight_globdef_assign_loc_value_only
      (ClightLang.cu_comp_env cu) gd.

(** The configuration-level projection used by finite executions. It looks
    only at the current statement. The program-level predicate above is the
    intended initialization premise; connecting it to arbitrary reachable
    cores still requires a core-provenance invariant. *)
Definition clight_core_assign_loc_value_syntax
    (ge : Clight.genv) (c : Clight_core.CC_core) : Prop :=
  match c with
  | Clight_core.State _ (Clight.Sassign lhs _) _ _ _ =>
      clight_assign_loc_value_lhs ge.(Clight.genv_cenv) lhs
  | _ => True
  end.

Lemma clight_full_lvalue_syntax_sound
    ge e le m lhs loc ofs bf T :
  clight_full_lvalue_syntax ge.(Clight.genv_cenv) lhs ->
  Clight_evsem.eval_lvalueT ge e le m lhs loc ofs bf T ->
  bf = Ctypes.Full.
Proof.
  intros Hsyntax Heval.
  inversion Hsyntax; subst; inversion Heval; subst; try reflexivity;
    congruence.
Qed.

(** The two static checks force the unique ordinary store constructor and
    expose its exact trace. *)
Lemma clight_assign_locT_value_of_syntax
    ge e le m lhs loc ofs bf Tlhs v m' Tstore :
  clight_assign_loc_value_lhs ge.(Clight.genv_cenv) lhs ->
  Clight_evsem.eval_lvalueT ge e le m lhs loc ofs bf Tlhs ->
  Clight_evsem.assign_locT ge (Clight.typeof lhs)
    m loc ofs bf v m' Tstore ->
  exists chunk,
    Ctypes.access_mode (Clight.typeof lhs) = Ctypes.By_value chunk /\
    Mem.storev chunk m (Vptr loc ofs) v = Some m' /\
    Tstore =
      [event_semantics.Write loc (Ptrofs.unsigned ofs)
         (Memdata.encode_val chunk v)].
Proof.
  intros [Hfull [chunk Hmode]] Heval Hassign.
  pose proof
    (clight_full_lvalue_syntax_sound
      ge e le m lhs loc ofs bf Tlhs Hfull Heval) as Hbf.
  subst bf.
  inversion Hassign; subst.
  - eexists. repeat split; eauto.
  - congruence.
Qed.

(** For a non-assignment core the predicate is vacuous.  For an assignment
    it exposes exactly the premises of [Clight_evsem.assign_locT_value], as
    well as the raw event trace and successor core produced by
    [Clight_evsem.evstep_assign]. *)
Definition clight_evstep_assign_loc_value_only
    (ge : Clight.genv) (c : Clight_core.CC_core) (m : mem)
    (T : list event_semantics.mem_event)
    (c' : Clight_core.CC_core) (m' : mem) : Prop :=
  match c with
  | Clight_core.State f (Clight.Sassign a1 a2) k e le =>
      exists loc ofs v2 v chunk T1 T2,
        Clight_evsem.eval_lvalueT ge e le m a1 loc ofs Ctypes.Full T1 /\
        Clight_evsem.eval_exprT ge e le m a2 v2 T2 /\
        Cop.sem_cast v2 (Clight.typeof a2) (Clight.typeof a1) m = Some v /\
        Ctypes.access_mode (Clight.typeof a1) = Ctypes.By_value chunk /\
        Mem.storev chunk m (Vptr loc ofs) v = Some m' /\
        T = T1 ++ T2 ++
          [event_semantics.Write loc (Ptrofs.unsigned ofs)
             (Memdata.encode_val chunk v)] /\
        c' = Clight_core.State f Clight.Sskip k e le
  | _ => True
  end.

Lemma clight_evstep_assign_loc_value_only_of_syntax
    ge c m T c' m' :
  clight_core_assign_loc_value_syntax ge c ->
  event_semantics.ev_step (Clight_evsem.CLC_evsem ge)
    c m T c' m' ->
  clight_evstep_assign_loc_value_only ge c m T c' m'.
Proof.
  destruct c as [f s k e le | fd args k | v k].
  - destruct s; simpl; try tauto.
    intros Hsyntax Hstep.
    change (Clight_evsem.cl_evstep ge
      (Clight_core.State f (Clight.Sassign e0 e1) k e le)
      m T c' m') in Hstep.
    dependent destruction Hstep.
    + assert (Hbf : bf = Ctypes.Full).
      { eapply clight_full_lvalue_syntax_sound; eauto.
        exact (proj1 Hsyntax). }
      subst bf.
      destruct (clight_assign_locT_value_of_syntax
        ge e le m e0 loc ofs Ctypes.Full T1 v m' T3 Hsyntax H H2)
        as (chunk & Hmode & Hmem & HT).
      subst T3.
      do 7 eexists.
      repeat split; eauto.
    + destruct H; discriminate.
    + destruct H; discriminate.
  - simpl; auto.
  - simpl; auto.
Qed.

(** The atomic machine stores the byte-expanded trace [clight_into_evs T]. *)
Definition clight_core_step_assign_loc_value_only
    (ge : Clight.genv) (c : Clight_core.CC_core) (m : mem)
    (T : list (@mem_ev address))
    (c' : Clight_core.CC_core) (m' : mem) : Prop :=
  exists rawT,
    event_semantics.ev_step (Clight_evsem.CLC_evsem ge)
      c m rawT c' m' /\
    T = clight_into_evs rawT /\
    clight_evstep_assign_loc_value_only ge c m rawT c' m'.

Lemma clight_core_step_assign_loc_value_only_of_syntax
    ge c m T c' m' :
  clight_core_assign_loc_value_syntax ge c ->
  ev_step_with_mem_ev (Clight_evsem.CLC_evsem ge) c m T c' m' ->
  clight_core_step_assign_loc_value_only ge c m T c' m'.
Proof.
  intros Hsyntax Hstep.
  inversion Hstep; subst; clear Hstep.
  eexists. repeat split; eauto using
    clight_evstep_assign_loc_value_only_of_syntax.
Qed.
