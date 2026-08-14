(** A marker-enabled variant of CASCompCert's second Clight interaction
    semantics.

    [ClightLang.Clight_IS_2] deliberately hides [GAST.ent_atom] and
    [GAST.ext_atom] in its [at_external] function.  This file defines a
    contained language for atomic-wrapper modules.  It reuses every component
    of [Clight_IS_2] except the external-call boundary.  Ordinary resolved
    [EF_external] calls retain their old behavior, while the two exact
    [EF_builtin] marker calls are exposed directly to the global semantics. *)

Require Import compcert.lib.Coqlib.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Values.
Require Import compcert.cfrontend.Clight.

Require Import compcert.concurrency.common.GAST.
Require Import compcert.concurrency.common.InteractionSemantics.
Require Import compcert.concurrency.common.clight_val_casted.
Require Import compcert.concurrency.comp_correct.ClightLang.

From Stdlib Require Import List.
From Stdlib Require Import Strings.String.

Import ListNotations.
Local Open Scope string_scope.

(** [ClightLang.invert_symbol_from_string] deliberately considers only
    [EF_external] definitions.  The wrapper markers below are [EF_builtin]s,
    so recognize their two reserved name/signature pairs directly instead of
    attempting to invert their global blocks. *)
Definition clight_is2_builtin_marker
    (name : string) (sig : signature) : option ident :=
  if string_dec name "ent_atom" then
    if signature_eq sig GAST.ent_atom_sg
    then Some GAST.ent_atom
    else None
  else if string_dec name "ext_atom" then
    if signature_eq sig GAST.ext_atom_sg
    then Some GAST.ext_atom
    else None
  else None.

(** Add the two exact marker builtins and delegate every other state to the
    original [ClightLang.at_external].  In particular, ordinary client calls
    retain the original definedness and reserved-identifier filters. *)
Definition clight_is2_markers_at_external
    (ge : Clight.genv) (c : ClightLang.core) :
    option (ident * signature * list val) :=
  match c with
  | ClightLang.Core_Callstate
      (Ctypes.External (EF_builtin name sig) _ _ _) [] _ =>
      match clight_is2_builtin_marker name sig with
      | Some fnid => Some (fnid, sig, [])
      | None => ClightLang.at_external ge c
      end
  | _ => ClightLang.at_external ge c
  end.

(** Resume exact marker builtins after [GlobSemantics.Ent_Atom] or
    [GlobSemantics.Ext_Atom].  All other calls retain
    [ClightLang.after_external], in particular the existing [EF_external]
    behavior used by compatibility lemmas below. *)
Definition clight_is2_markers_after_external
    (c : ClightLang.core) (rv : option val) : option ClightLang.core :=
  match c with
  | ClightLang.Core_Callstate fd args k =>
      match fd, args, rv with
      | Ctypes.External (EF_builtin name sig) _ _ _, [], None =>
          match clight_is2_builtin_marker name sig with
          | Some _ => Some (ClightLang.Core_Returnstate Vundef k)
          | None => ClightLang.after_external c rv
          end
      | _, _, _ => ClightLang.after_external c rv
      end
  | _ => ClightLang.after_external c rv
  end.

(** A contained marker-enabled target language.  Its core, initialization,
    internal steps, halt predicate, and global-environment/memory
    initialization are definitionally the ones from
    [ClightLang.Clight_IS_2]; only the two external-boundary functions differ. *)
Definition Clight_IS_2_with_markers : Language :=
  Build_Language
    Clight.fundef Ctypes.type Clight.genv
    ClightLang.clight_comp_unit ClightLang.core
    ClightLang.init_core ClightLang.step2
    clight_is2_markers_at_external clight_is2_markers_after_external
    ClightLang.halted ClightLang.internal_fn
    ClightLang.init_genv ClightLang.init_gmem.

Lemma clight_is2_markers_preserves_external :
  forall (ge : Clight.genv) name sig targs tres cc args k,
    clight_is2_markers_at_external ge
      (ClightLang.Core_Callstate
        (Ctypes.External (EF_external name sig) targs tres cc) args k) =
    ClightLang.at_external ge
      (ClightLang.Core_Callstate
        (Ctypes.External (EF_external name sig) targs tres cc) args k).
Proof. reflexivity. Qed.

Lemma clight_is2_markers_exposes_builtin :
  forall (ge : Clight.genv) name sig fnid targs tres cc k,
    clight_is2_builtin_marker name sig = Some fnid ->
    clight_is2_markers_at_external ge
      (ClightLang.Core_Callstate
        (Ctypes.External (EF_builtin name sig)
          targs tres cc) [] k) =
      Some (fnid, sig, []).
Proof.
  intros ge name sig fnid targs tres cc k Hmarker.
  simpl. rewrite Hmarker. reflexivity.
Qed.

(** A non-marker builtin still follows the original boundary behavior.  This
    regression lemma prevents the adapter from accidentally widening the
    external-call interface when new builtin forms are added. *)
Lemma clight_is2_markers_preserves_nonmarker_builtin :
  forall (ge : Clight.genv) name sig targs tres cc k,
    clight_is2_builtin_marker name sig = None ->
    clight_is2_markers_at_external ge
      (ClightLang.Core_Callstate
        (Ctypes.External (EF_builtin name sig) targs tres cc) [] k) =
    ClightLang.at_external ge
      (ClightLang.Core_Callstate
        (Ctypes.External (EF_builtin name sig) targs tres cc) [] k).
Proof.
  intros ge name sig targs tres cc k Hnot_marker.
  simpl. rewrite Hnot_marker. reflexivity.
Qed.

Lemma clight_is2_markers_preserves_after_external :
  forall name sig targs tres cc args k rv,
    clight_is2_markers_after_external
      (ClightLang.Core_Callstate
        (Ctypes.External (EF_external name sig) targs tres cc) args k)
      rv =
    ClightLang.after_external
      (ClightLang.Core_Callstate
        (Ctypes.External (EF_external name sig) targs tres cc) args k)
      rv.
Proof. reflexivity. Qed.

Lemma clight_is2_markers_after_builtin :
  forall name sig fnid targs tres cc k,
    clight_is2_builtin_marker name sig = Some fnid ->
    InteractionSemantics.after_external Clight_IS_2_with_markers
      (ClightLang.Core_Callstate
        (Ctypes.External (EF_builtin name sig)
          targs tres cc) [] k)
      None =
    Some (ClightLang.Core_Returnstate Vundef k).
Proof.
  intros name sig fnid targs tres cc k Hmarker.
  simpl. rewrite Hmarker. reflexivity.
Qed.

Lemma clight_is2_markers_preserves_after_nonmarker_builtin :
  forall name sig targs tres cc k,
    clight_is2_builtin_marker name sig = None ->
    clight_is2_markers_after_external
      (ClightLang.Core_Callstate
        (Ctypes.External (EF_builtin name sig) targs tres cc) [] k)
      None =
    ClightLang.after_external
      (ClightLang.Core_Callstate
        (Ctypes.External (EF_builtin name sig) targs tres cc) [] k)
      None.
Proof.
  intros name sig targs tres cc k Hnot_marker.
  simpl. rewrite Hnot_marker. reflexivity.
Qed.
