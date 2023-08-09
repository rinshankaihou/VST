Require Import mathcomp.ssreflect.fintype List.
Require Import compcert.lib.Coqlib compcert.common.Errors compcert.common.AST.
Require Import InteractionSemantics.


(** * Definitions for global AST *)

(** There are special idents 
    - [print] : corresponds to event message 
    - [ent_atom] : corresponds to enter atomic block message
    - [exit_atom] : corresponds to exit atomic block message
    These idents are hardwired in the global syntax and semantics,
    and are not supposed to be bound to user defined global definitions in modules.
 *)
Definition print : ident := 1%positive.
Definition ent_atom : ident := 2%positive.
Definition ext_atom : ident := 3%positive.

Definition print_sg: signature := 
  {| sig_args := Tint :: nil; sig_res := Tvoid; sig_cc := cc_default |}.
Definition ent_atom_sg: signature :=
  {| sig_args := nil; sig_res := Tvoid; sig_cc := cc_default |}.
Definition ext_atom_sg: signature :=
  {| sig_args := nil; sig_res := Tvoid; sig_cc := cc_default |}.

Definition not_primitive: ident -> Prop :=
  fun id =>
    if peq id print then False
    else if peq id ent_atom then False
         else if peq id ext_atom then False
              else True.

Lemma not_primitive_cases:
  forall id, not_primitive id ->
        id <> print /\ id <> ent_atom /\ id <> ext_atom.
Proof.
  unfold not_primitive; intros; repeat destruct peq; intuition.
Qed.

Ltac not_prim :=
  match goal with
  | H: not_primitive _ |- _ =>
    apply not_primitive_cases in H; destruct H as (?&?&?)
  end.
    
    
  
(** There are NL languages at source/target level *)
(* Why languages are implemented by finite mapping? *)
Definition langs {NL:nat} := 'I_NL -> Language.

Definition entry := ident.

(** entries are modeled as list of [entry] *)
Definition entries := list entry. 

(** A compilation unit ([cunit]) consists of its corresponding language and a compilation unit *)
Record cunit {NL: nat} (L: langs): Type :=
  {
    lid: 'I_NL;
    cu: comp_unit (L lid);
  }.
(** [cunits] is a mapping from module id to its [cunit], 
    modeled as list instead of a finite map *)
Definition cunits {NL: nat} (L: langs) := list (@cunit NL L).
(* Definition cunits {NL: nat} (L: langs) {M: nat} := 'I_M -> @cunit NL L.*)

(** Program is a pair of compilation units and thread entries *)
Definition prog {NL: nat} (L: @langs NL) : Type :=
  @cunits NL L * entries .


(** languages of compilation units are well-defined *)
Definition wd_langs {NL: nat} {L: @langs NL}: @cunits NL L -> Prop :=
  fun cus => forall cu, In cu cus -> wd (L cu.(lid L)).
(** languages of compilation units are deterministic *)
Definition det_langs {NL: nat} {L: @langs NL}: @cunits NL L -> Prop :=
  fun cus => forall cu, In cu cus -> lang_det (L cu.(lid L)).



(** * Definition of Compilation *)

(** There is a compiler for each compilation unit *)

(** A single compiler is parameterized with the source and target languages *)

Record seq_comp_i {NL: nat} {L: langs} : Type :=
  {
    slid: 'I_NL;
    tlid: 'I_NL;
    comp: @seq_comp (L slid) (L tlid);
  }.


(** [gcomp] is a collection of compilers, modeled as a list *)
Definition gcomp {NL: nat} {L: @langs NL} : Type := list (@seq_comp_i NL L).
  

(** Cunit transformation *)
Inductive cunit_transf {NL: nat} {L: langs} :
  seq_comp_i -> cunit L -> cunit L -> Prop :=
| Transf_cunit:
    forall scomp scu tcu slid scomp_unit tlid tcomp_unit comp,
      scomp = Build_seq_comp_i NL L slid tlid comp ->
      scu = Build_cunit NL L slid scomp_unit ->
      tcu = Build_cunit NL L tlid tcomp_unit ->
      comp scomp_unit = OK tcomp_unit ->
      cunit_transf scomp scu tcu.

Inductive cunits_transf {NL: nat} {L: langs} :
  gcomp -> cunits L -> cunits L -> Prop :=
| Trans_nil: cunits_transf nil nil nil
| Trans_cons: 
    forall scomp scu tcu comp scus tcus,
      @cunit_transf NL L scomp scu tcu ->
      cunits_transf comp scus tcus ->
      cunits_transf (scomp::comp) (scu::scus) (tcu::tcus).

Lemma cunits_transf_wf:
  forall NL L comp scus tcus,
    @cunits_transf NL L comp scus tcus ->
    forall i, 
      (exists scu tcu scomp,
          nth_error scus i = Some scu /\
          nth_error tcus i = Some tcu /\
          nth_error comp i = Some scomp /\
          cunit_transf scomp scu tcu) \/
      (nth_error scus i = None /\
       nth_error tcus i = None /\
       nth_error comp i = None).
Proof.
  intros NL L comp0 scus tcus H.
  induction H; intro.
  - repeat rewrite nth_error_nil; auto.
  - destruct i.
    simpl. left. exists scu, tcu, scomp. auto.
    simpl. apply IHcunits_transf.
Qed.
    
