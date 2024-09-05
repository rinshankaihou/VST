(* Do not edit this file, it was generated automatically *)
Require Import VST.concurrency.conclib.
Require Import VST.concurrency.lock_specs.
Require Import VST.atomics.SC_atomics.
From diaframe Require Import defs weakestpre.
From diaframe Require Export spec_notation.
From diaframe Require Import proofmode_base.
From diaframe.lib Require Import iris_hints.
From iris.proofmode Require Import base coq_tactics reduction tactics string_ident.
From Ltac2 Require Import Int Option Ltac1 Ltac2 Printf.

Import LiftNotation.

Set Default Proof Mode "Classic".

Definition wp_def {OK_ty : Type} {Σ : gFunctors} {VSTGS0 : VSTGS OK_ty Σ} {Espec} {cs:compspecs} (E:coPset) (Delta: tycontext) (c: statement) (Q: ret_assert): assert :=
  ∃ P: assert, ⌜@semax OK_ty Σ VSTGS0 Espec cs E Delta P c Q⌝ ∧ P.
Definition wp_aux : seal (@wp_def). by eexists. Qed.
Definition wp := unseal wp_aux.
Definition wp_eq : @wp = @wp_def := seal_eq wp_aux.

(* Notation wp OK_ty Σ VSTGS0 Espec cs E Delta c Q := (∃ P: assert, ⌜@semax OK_ty Σ VSTGS0 Espec cs E Delta P c Q⌝ ∧ P). *)
Definition wp_spec: forall {OK_ty : Type} {Σ : gFunctors} {VSTGS0 : VSTGS OK_ty Σ} {Espec} {cs:compspecs} (E:coPset) (Delta: tycontext) P c Q,
  (P ⊢ @wp OK_ty Σ VSTGS0 Espec cs E Delta c Q) <-> @semax OK_ty Σ VSTGS0 Espec cs E Delta P c Q.
Proof.
  intros.
  split; intros.
  + eapply semax_pre.
    - rewrite bi.and_elim_r H //.
    - rewrite wp_eq.
      apply semax_extract_exists.
      clear P H.
      intros P.
      apply semax_extract_prop.
      auto.
  + rewrite wp_eq.
    iIntros; iExists P; iSplit; auto.
Qed.

(* explicitly gain Delta from semax *)
Definition wp_spec_Delta: forall {OK_ty : Type} {Σ : gFunctors} {VSTGS0 : VSTGS OK_ty Σ} {Espec} {cs:compspecs} (E:coPset) (Delta: tycontext) P c Q,
  (ENTAIL Delta, P ⊢ @wp OK_ty Σ VSTGS0 Espec cs E Delta c Q) <-> @semax OK_ty Σ VSTGS0 Espec cs E Delta P c Q.
Proof.
  intros. rewrite wp_spec.
  split; apply semax_pre.
  - done. 
  - iSteps.
Qed.

(* from vst *)

(* change goal from semax to `hyp ⊢ monPred_at (wp ...) rho` *)
Ltac into_ipm := rewrite -?seq_assoc; rewrite <- wp_spec_Delta; go_lowerx.

#[global] Typeclasses Opaque locald_denote.
Arguments locald_denote : simpl never.

#[global] Instance into_and_local `{!heapGS Σ} p P Q : IntoAnd p (local (`(and) P Q)) (local P) (local Q).
Proof. by rewrite /IntoAnd local_lift2_and. Qed.

(* for diaframe *)
#[global] Instance into_sep_local  `{!heapGS Σ} P Q: IntoSep (local (`(and) P Q)) (local P) (local Q).
Proof. rewrite /IntoSep. rewrite local_lift2_and. iIntros "[#$ #$]". Qed.

#[global] Instance into_sep_careful_local  `{!heapGS Σ} P Q: IntoSepCareful (local (`(and) P Q)) (local P) (local Q).
Proof. rewrite /IntoSepCareful local_lift2_and. iIntros "[#$ #$]". Qed.

(* maybe turn this into something more general, but we need to prove BiPositive mpred *)
#[global] Instance into_sep_careful_affine_local  `{!heapGS Σ} P Q: IntoSepCareful (<affine> local (`(and) P Q)) (<affine> local P) (<affine> local Q).
Proof. rewrite /IntoSepCareful local_lift2_and // bi.affinely_and. iIntros "[#$ #$]". Qed.

#[global] Instance into_sep_careful_local_foldr_and  `{!heapGS Σ} P Qs: IntoSepCareful (local (foldr (` and) (` True%type) (map locald_denote (P::Qs)))) 
                                                                         (local (locald_denote P)) (local (foldr (` and) (` True%type) (map locald_denote Qs))).
Proof. rewrite /IntoSepCareful. simpl. rewrite local_lift2_and. iIntros "[#$ #$]". Qed.

#[global] Instance comine_sep_as_local  `{!heapGS Σ} P: CombineSepAs (local (liftx True%type)) 
                                                          (local (locald_denote P))
                                                          (local (foldr (` and) (` True%type) (map locald_denote [P]))).
Proof. rewrite /CombineSepAs. rewrite !local_lift2_and. iIntros "[#? #?]"; iFrame "#". Qed.

#[global] Instance comine_sep_as_local_2  `{!heapGS Σ} P Qs: CombineSepAs (local (foldr (` and) (` True%type) (map locald_denote Qs)))
                                                               (local (locald_denote P))
                                                               (local (foldr (` and) (` True%type) (map locald_denote (P::Qs)))).
Proof. rewrite /CombineSepAs. rewrite !local_lift2_and. iIntros "[#? #?]"; iFrame "#". Qed.

(* SEP *)
#[global] Instance into_sep_careful_SEP {A Σ'} P Q R: IntoSepCareful (@SEPx A Σ' (P::Q::R)) (SEPx [P]) (SEPx (Q::R)).
Proof. rewrite /IntoSepCareful. iIntros "[$ $]". Qed.

(* P is singleton *)
(* #[global] Instance combine_sep_as_SEP_1 {A Σ'} P Q R: CombineSepAs (SEPx [P]) (SEPx (Q::R)) (@SEPx A Σ' (P::Q::R)).
Proof. rewrite /CombineSepAs /SEPx -!embed_sep /fold_right_sepcon bi.sep_emp //. Qed. *)

#[global] Instance combine_sep_as_SEP {A Σ'} P Q R: CombineSepAs (SEPx (Q::R)) (SEPx [P]) (@SEPx A Σ' (P::Q::R)).
Proof. rewrite /CombineSepAs /SEPx -!embed_sep /fold_right_sepcon bi.sep_emp. rewrite [_ ∗ P]bi.sep_comm //. Qed.

#[global] Instance combine_sep_as_fold_right_sep_con {prop:bi} (P: prop) (Q: list prop): CombineSepAs (fold_right_sepcon Q) (fold_right_sepcon [P]) (fold_right_sepcon $ P::Q).
Proof. rewrite /CombineSepAs. simpl. iSteps. Qed.



(* select 2 different hyps that match pat1 and pat2 respectively *)
Tactic Notation "iSelect2" open_constr(pat1) open_constr(pat2) tactic1(tac) :=
lazymatch goal with
| |- context[ environments.Esnoc _ ?x pat1 ] =>
  lazymatch iTypeOf x with
  | Some (_,?T) => unify T pat1;
    match goal with
    | |- context[ environments.Esnoc _ ?y pat2 ] =>
      lazymatch iTypeOf y with
      | Some (_,?T) => (assert_fails (unify x y)); unify T pat2; tac x y
      end
    end
  end
end.

Tactic Notation "_iCombine" constr(H1) constr(H2):=
iCombine [H1;H2] as "?".

Tactic Notation "Combine" open_constr(pat1) open_constr(pat2):=
  iSelect2 pat1 pat2 
  ltac:(fun x y => iRename x into "__VerySecretName1";
                   iRename y into "__VerySecretName2"; 
                   iCombine "__VerySecretName1" "__VerySecretName2" as "?";
                   try iClear "__VerySecretName1 __VerySecretName2").

#[global] Typeclasses Opaque SEPx.
#[global] Typeclasses Opaque local. (* do same thing as sepx so it is always LOCALx*)
#[global] Typeclasses Opaque field_at.
#[global] Typeclasses Opaque tc_environ.

#[global] Instance combine_sep_as_PQR `{!heapGS Σ} (Q: list localdef) R: CombineSepAs (SEPx R)
  (<affine> local (foldr (liftx and) (liftx True%type) (map locald_denote Q)))
  (PROP () (LOCALx Q (SEPx R))).
Proof. rewrite /CombineSepAs /PROPx /LOCALx /SEPx. iIntros "($ & #$)". Qed.


#[global] Instance semax_mono: ∀ {OK_ty : Type} {Σ' : gFunctors} {VSTGS0 : VSTGS OK_ty Σ'} 
{OK_spec : ext_spec OK_ty} {CS : compspecs} (E : coPset) (Delta : tycontext),
  Proper (bi_entails ==> eq ==> equiv ==> flip impl)
         (semax E Delta).
Proof. intros. rewrite /Proper /respectful /flip /impl. intros ?????->??->. by apply ConseqFacts.semax_pre_simple. Qed.

Lemma add_PROPx : forall `{!heapGS Σ} Q R, (LOCALx Q (SEPx R) ⊣⊢ PROP ( ) (LOCALx Q (SEPx R)))%assert5.
Proof. intros. unfold PROPx; simpl. rewrite bi.True_and //. Qed.

#[global] Instance comine_sep_as_Delta_PQR `{!heapGS Σ} P Q R Delta:
CombineSepAs (<affine> local (tc_environ Delta)) 
             (@PROPx _ Σ P (LOCALx Q (SEPx R)))
             (local (tc_environ Delta) ∧ (PROPx P (LOCALx Q (SEPx R)))).
Proof. rewrite /CombineSepAs. rewrite -bi.persistent_and_affinely_sep_l. rewrite comm //. Qed.

Ltac from_ipm :=
  match goal with 
  | |- envs_entails _ (wp _ _ _ _) =>
      (* if goal is wp, Delta is already in wp and redundant *)
      iSelect (local (tc_environ _)) (fun x => iClear x)
  | _ => 
      (* otherwise, keep it, move to spatial context for merging *)
    idtac
  end;
  (* Combine LOCALs, base case and then recurive case *)
  Combine (local (liftx True%type)) (local (locald_denote _));
  repeat Combine (local (foldr (liftx and) _ _)) (local (locald_denote _));
  (* Combine SEPs *)
  repeat Combine (SEPx _) (SEPx _);
  (* move LOCAL to spatial context, Combine with SEP *)
  iSelect (local (foldr (liftx and) _ _ )) (fun x => iDestruct x as "-#?");
  Combine (SEPx _) (<affine> local (foldr (liftx and) _ _ ));
  lazymatch goal with
  | |- envs_entails _ (wp _ _ _ _) => idtac
  | _ => iSelect (local (tc_environ _)) (fun x => iDestruct x as "-#?");
          Combine (<affine> local (tc_environ _)) (PROPx _ _)
  end;
  iStopProof;
  lazymatch goal with
  | |- _ ⊢ wp _ _ _ _ =>
      rewrite -> ?wp_spec
  | _ => idtac
  end
  .


Lemma into_fold_right_sepcon_singleton : forall {Σ:gFunctors} (P: iProp Σ),
  P ⊣⊢ fold_right_sepcon [P].
Proof. intros. iSteps. Qed.

Ltac into_fold_right_sepcons Γs :=
lazymatch Γs with
|  Esnoc ?Γs' _ (fold_right_sepcon _) => idtac
|  Esnoc ?Γs' _ ?P => rewrite [(X in (Esnoc Γs' _ X))](into_fold_right_sepcon_singleton P);
                      into_fold_right_sepcons Γs'
| _ => idtac 
end.

(* assume in ipm, change every hyp in the sep context to "fold_right_sepcon [hyp]" *)
Ltac into_fold_right_sepcons_Γs :=
match goal with
| |- envs_entails (Envs _ ?Γs _) _ =>
  into_fold_right_sepcons Γs
end.


Lemma change_SEP `{!VSTGS unit Σ} E d P Q (R: list mpred) (R' R'': list mpred):
  (fold_right_sepcon R ⊢  |={E}=> fold_right_sepcon $ (R'++ R'')) ->
    local (tc_environ d) ∧ PROPx P $ LOCALx Q $ SEPx R ⊢ PROPx P $ LOCALx Q $ |={E}=> (SEPx $ R'++R'').
Proof. intros. go_lowerx. rewrite H //. Qed.

Lemma semax_change_pre:
 forall {OK_ty : Type} {Σ : gFunctors} {VSTGS0 : VSTGS OK_ty Σ} {Espec} {cs:compspecs} E Delta P Q R R' R'' c Post,
     (fold_right_sepcon R ⊢ fold_right_sepcon $ (R'++ R'')) ->
     @semax OK_ty Σ VSTGS0 Espec cs E Delta (PROPx P $ LOCALx Q $ SEPx (R'++R'')) c Post -> semax E Delta (PROPx P $ LOCALx Q $ SEPx R) c Post.
Proof.
intros until 1.
apply semax_pre_fupd. go_lowerx. rewrite H //. iIntros. done.
Qed.

Lemma semax_change_pre_for_forward_call:
  forall {OK_ty : Type} {Σ : gFunctors} {VSTGS0 : VSTGS OK_ty Σ} {Espec} {cs:compspecs} E Delta P Q R R' R'' c Post,
      (fold_right_sepcon R ⊢ |={E}=> fold_right_sepcon $ (R'++ R'')) ->
      @semax OK_ty Σ VSTGS0 Espec cs E Delta (PROPx P $ LOCALx Q $ SEPx (R'++R'')) c Post -> semax E Delta (PROPx P $ LOCALx Q $ SEPx R) c Post.
Proof.
intros until 1.
apply semax_pre_fupd. go_lowerx. rewrite H //.
Qed.

Ltac iCutL Q :=
  match goal with |- envs_entails _ ?P =>
    rewrite -[P](bi.wand_elim_r Q) end.

Lemma cut_with_exists_tac {prop:bi} {A:Type} (P: A -> prop) (Q:prop):
  (∃ x, (P x ∗ (P x -∗ Q))) ⊢ Q.
Proof. iSteps. Qed.

Lemma cut_with_exists_tac2 {prop:bi} {A B:Type} (P: A -> B -> prop) (Q:prop):
  (∃ x y, (P x y ∗ (P x y -∗ Q))) ⊢ Q.
Proof. iSteps. Qed.

Ltac2 is_Sset cmd :=
  match! cmd with 
    | Ssequence (Sset _ _) _ => true
    | Sset _ _  => true
    | _ => false
  end.

Ltac2 get_gv () :=
  match! goal with
  | [ gv : globals |- _] => gv
  end.

(* get a list of localdefs from the context *)
(* Ltac2 get_locals () := *)
Ltac2 rec get_locals_helper (ls: (ident * constr option * constr) list) : constr :=
  match ls with 
  | (_, _, ty) :: ls' =>
    match! ty with 
    | locald_denote ?t _ =>
     let locals' := (get_locals_helper ls') in constr:(@cons localdef $t $locals')
    | _ => get_locals_helper ls'
    end
  | [] => constr:(@nil localdef)
  end.

(* get a list of localdefs from the context *)
Ltac2 get_locals () :=
  get_locals_helper (Control.hyps ()).

Ltac monPred_at_wp_to_semax :=
  iStopProof;
  rewrite ?bi.True_sep ?bi.sep_emp;
  rewrite wp_eq /wp_def;
  iIntros "?";
  iExists _;
  iSplit; last first; 
  [ iStartProof;
    let locals := ltac2val:(Ltac1.of_constr (get_locals ())) in
    instantiate (1:= PROPx nil $ LOCALx locals $ SEPx [_]);
    unfold PROPx, LOCALx, SEPx;
    monPred.unseal;
    rewrite bi.True_and !bi.sep_emp;
    iSplit; [done|iAccu]
  | iPureIntro];
  Intros.

(* goal has the form `_ ⊢ g` *)
Ltac2 pose_Sset_pre (cmd:constr) (g:constr):=
  lazy_match! cmd with
      | context [Sset _ (Efield (Evar ?_struct_id ?struct_type) ?_field_id _)] =>
        ltac1:(G struct_type _field_id _struct_id gv |-
               rewrite -[G](cut_with_exists_tac2 (fun sh z => field_at sh struct_type (DOT _field_id) z (gv _struct_id)) G))
        (Ltac1.of_constr g) (Ltac1.of_constr struct_type) (Ltac1.of_constr _field_id) (Ltac1.of_constr _struct_id) (Ltac1.of_ident (get_gv ()))
      | _ => Control.throw (Invalid_argument (Some (Message.of_string "unimplemented shape of Sset` ")))
    end.


Ltac2 vstep_forward_abd_pre () :=
  ltac1:(into_ipm);
  let g := lazy_match! goal with
    | [|- _ ⊢ ?g] => g
    | [|- _ ] => Control.throw (Invalid_argument (Some (Message.of_string "expect goal to be an entailment; did you do `rewrite -?seq_assoc; into_ipm; go_lowerx`?"))) end in
  let cmd := lazy_match! g with
    | monPred_at (wp _ _ _ _ _ _ _ ?cmd _) _ => cmd
    | _ => Control.throw (Invalid_argument (Some (Message.of_string "expect goal to be `monPred_at (wp ...)` "))) end in
  (* assert precondition that forward needs *)
  if is_Sset cmd then pose_Sset_pre cmd g 
  else ();
  (* solve asserted precondition *)
  ltac1:(iSteps);
  (* restore goal shape to semax *)
  ltac1:(monPred_at_wp_to_semax);
  ltac1:(rho |- clear dependent rho) (Ltac1.of_ident (Option.get (Ident.of_string "rho")))
.

Ltac2 vstep_forward () :=
  Control.plus (fun () => ltac1:(forward))
               (fun _ => vstep_forward_abd_pre (); ltac1:(forward)).

 (* from get_function_witness_type *)
Ltac pose_witness_type (*ts*) Σ A witness :=
  (unify A (ConstType Ridiculous); (* because [is_evar A] doesn't seem to work *)
             exfalso)
 ||
 let TA := constr:(ofe_car (@dtfr Σ A)) in
  let TA' := eval cbv [dtfr dependent_type_functor_rec constOF idOF prodOF discrete_funOF
      ofe_morOF sigTOF list.listOF oFunctor_car ofe_car] in TA
 in let TA'' := eval simpl in TA'
  in match type of witness with ?T => 
       (unify T TA''; let ARG:=fresh "ARG" in pose witness as ARG)
      + (fail "Type of witness does not match type required by funspec WITH clause.
Witness value: " witness "
Witness type: " T "
Funspec type: " TA'')
     end.

(* from prove_call_setup *)
Ltac get_pre_sep_of_spec subsumes witness :=
prove_call_setup1 subsumes
;
[ .. | 
match goal with |- @call_setup1 _ ?Σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?A _ _ _ _  -> _ =>
pose_witness_type (*ts*) Σ A witness
end
]
.

Lemma emp_fold_right_sepcon_nil {prop:bi} : emp ⊣⊢@{prop} fold_right_sepcon [].
Proof. reflexivity. Qed.

Ltac change_pre_sep_with fpre_sep :=
eapply (semax_change_pre_for_forward_call _ _ _ _ _ fpre_sep);
[
cbn;
iSteps;
into_fold_right_sepcons_Γs;
repeat (Combine (fold_right_sepcon _) (fold_right_sepcon _));
iStopProof; rewrite -fupd_intro;
match goal with
    | |- emp ⊢ fold_right_sepcon _ => rewrite emp_fold_right_sepcon_nil
    | _ => idtac
end;    
f_equal
| simpl app].


#[global] Opaque lock_handle. (* FIXME change this to seal *)


Ltac2 rec evar_tuple (ty: constr) : (constr * ident list) :=
  let ty := eval hnf in $ty in (* allows you to pass `ty` instead of having to pass `(nat * (bool * nat))%type` *)
  lazy_match! ty with
  | prod ?a ?b =>
      let (evar_a, l_a) : (constr *  ident list) := evar_tuple a in
      let (evar_b, l_b) : (constr *  ident list) := evar_tuple b in
      ( constr:(@pair $a $b $evar_a $evar_b), (List.append  l_a  l_b)) (* typing constraints on the evars are enforced here;
note that this will give you an evar with evar type,
rather than a typed evar, if you pass it a type that is not a prod *)
  | ?a =>
      let arg_i := Fresh.in_goal @h in (* this uses base name "h" *)
      epose _ as $arg_i; (* _ gives a new evar, use '_ or open_constr:(_) in other contexts *)
      (Control.hyp arg_i, [arg_i])
  end.

Ltac2 rec subst_tuple t : ident :=
  lazy_match! t with
  | pair ?x ?y =>
      subst_tuple x

  | ?x => lazy_match! goal with
          | [ x := _ |- _] => x end
  end.

(* name of function (an AST.ident), a list of spec subsume relations to try  *)
Ltac2 Type vstep_specs_type := (constr * constr) list.
Ltac2 mutable vstep_specs : unit -> vstep_specs_type  := fun _ => [].

Ltac2 rec get_specs_for_aux (f_id: constr) (specs: vstep_specs_type) :=
    match specs with
    | [] => []
    | (f', sub)::t => Control.plus (fun () => Std.unify f_id f'; sub :: (get_specs_for_aux f_id t))
                                   (fun _ => get_specs_for_aux f_id t)
    end.

Ltac2 get_specs_for (f_id: constr) :=
  let specs := vstep_specs () in
  get_specs_for_aux f_id specs.


(* FIXME use the string version of the _release ident instead of constr? *)
(* Ltac2 Set vstep_specs as old_vstep_specs :=
  fun _ => (constr:(_release), constr:(release_simple))::
           (constr:(_acquire), constr:(funspec_sub_refl_dep))::
           (old_vstep_specs ()). *)

 
Ltac vstep_call_preprocess :=
   (* from forward_call i.e. new_fwd_call. *)
  try lazymatch goal with
        | |- semax _ _ _ (Scall _ _ _) _ => rewrite -> semax_seq_skip
        end;
  repeat lazymatch goal with
    | |- semax _ _ _ (Ssequence (Ssequence (Ssequence _ _) _) _) _ =>
        rewrite <- seq_assoc
  end
  .

Ltac2 get_body_of_localdef (name:ident) : constr :=
  match! goal with
  | [ h := ?body : _ |- _ ] => 
    if Ident.equal h name then body 
    else (fail; (* trigger backtrack *)
          constr:(tt) (* dead code; to make typechecker happy *))
  end.

Ltac2 print_syntax_kind (c:constr) :=
  printf "The constr %t has kind: " c;
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constant _ _ => printf "Constant"
  | Constr.Unsafe.Var _ => printf "Var"
  | Constr.Unsafe.App _ _ => printf "App"
  | Constr.Unsafe.Lambda _ _ => printf "Lambda"
  | Constr.Unsafe.Prod _ _ => printf "Prod"
  | Constr.Unsafe.LetIn _ _ _ => printf "LetIn"
  | Constr.Unsafe.Cast _ _ _ => printf "Cast"
  | Constr.Unsafe.Evar _ _ => printf "Evar"
  | Constr.Unsafe.Case _ _ _ _ _ => printf "Case"
  | Constr.Unsafe.Fix _ _ _ _ => printf "Fix"
  | Constr.Unsafe.CoFix _ _ _ => printf "CoFix"
  | Constr.Unsafe.Proj _ _ _ => printf "Proj"
  | Constr.Unsafe.Array _ _ _ _ => printf "Array"
  | Constr.Unsafe.Float _  => printf "Float"
  | Constr.Unsafe.Uint63 _ => printf "Uint63"
  | Constr.Unsafe.Constructor _ _ => printf "Constructor"
  | Constr.Unsafe.Ind _ _ => printf "Ind"
  | Constr.Unsafe.Sort _ => printf "Sort"
  | Constr.Unsafe.Meta _ => printf "Meta"
  | Constr.Unsafe.Rel _ => printf "Rel"
  end.



  Ltac2 mutable get_fpre_sep (sub:constr) (fun_ident:constr) :=
    let delta := match! goal with
                | [|-semax _ ?delta _ _ _] => delta end in
    let sp_name := lazy_match! sub with
      | funspec_sub_refl_dep =>  
        let maybe_sp_name := eval hnf in (PTree.get $fun_ident (glob_specs $delta)) in
        lazy_match! maybe_sp_name with
        | Some ?sp_name => sp_name
        | _ => Control.throw (Invalid_argument (Some (Message.of_string 
                "The function does not have a default spec!"))) end
      | _ => lazy_match! (Constr.type sub) with | funspec_sub _ ?sp_name => sp_name end end
    in
    let sp_name := eval hnf in $sp_name in
    (* print_syntax_kind sp_name; *)
    let sp := match (Constr.Unsafe.kind sp_name) with
              | Constr.Unsafe.Constant sp_def _ => let sp_ref :=  Std.ConstRef sp_def in eval unfold $sp_ref in $sp_name
              | _ => sp_name
              end in
    lazy_match! sp with
    | (mk_funspec _ _ _ _ ?fpre _) =>
    (* apply semax_extract_affine_sep > [apply _|]; *)
    match! fpre with λne _ : ?arg_type, _ =>
    let arg_type := eval cbn in $arg_type in
    let (arg_evar, evar_ids) := evar_tuple arg_type in
    let arg_evar_name := Fresh.in_goal @arg_evar in
    epose $arg_evar as $arg_evar_name;
    let fpre := constr:($fpre $arg_evar) in
    let fpre := eval cbn in $fpre in
    let fpre_sep_name := Fresh.in_goal @fpre_sep in
    lazy_match! fpre with | context [SEPx ?fpre_sep] =>
      pose $fpre_sep as $fpre_sep_name
    end;
    Std.subst evar_ids;
    clear sub;
    (fpre_sep_name, arg_evar_name)
    end end 
  .



Ltac2 vstep_call () :=
ltac1:(vstep_call_preprocess);
let fun_ident := match! goal with 
              | [ |- context [Scall _ (Evar ?fun_ident _)  _]] => fun_ident end in
let specs := get_specs_for fun_ident in
let rec try_specs sps fun_ident : unit :=
  match sps with
  | sp :: sps' => Control.plus (fun () => printf "In vstep_call: try applying spec %t" sp; 
                                          (* ltac1:(f_spec |- prove_call_setup1 f_spec) (Ltac1.of_constr sp); *)
                                            let (fpre_sep_name, arg_evar_name) := get_fpre_sep sp fun_ident in
                                            printf "2";
                                            ltac1:(fpre_sep |- change_pre_sep_with fpre_sep) (Ltac1.of_constr (Control.hyp fpre_sep_name));
                                            (* have to pass body of arg_evar_name, otherwise forward_call sometimes fails to unfold it *)
                                            let arg_evar_body:constr := get_body_of_localdef arg_evar_name in
                                            ltac1:(spec args |- forward_call spec args) (Ltac1.of_constr sp) (Ltac1.of_constr arg_evar_body);
                                            clear fpre_sep_name arg_evar_name)
                                (fun _ => printf "In vstep_call: applying %t failed" sp; try_specs sps' fun_ident) 
  | _ => () (* TODO explicitly fail here when all possible specs are tried? *)
  end 
in try_specs specs fun_ident.

(** tactics for cleanup after anything that runs iStep *)
Local Ltac2 Notation "red_flags" s(strategy) := s.
Ltac2 cbv_flags : Std.red_flags := (red_flags beta match fix cofix zeta delta).
(* TODO in newer versions of Coq, change to Ltac2.Ltac1.of_int/to_int *)
Ltac2 rec ltac2_int_to_gallina_int (n:int) : constr :=
  match n with
  | 0 => constr:(0)
  | _ => let v := (ltac2_int_to_gallina_int (Int.sub n 1)) in
          Std.eval_cbv cbv_flags constr:(1 + ltac2:(exact $v))
  end.

Ltac2 find_depth_of_affine_in_SEP () : int option :=
  match! goal with
    [ |- semax _ _ (PROPx _ (LOCALx _ (SEPx ?r))) _ _ ] =>
    let rec count_depth (r:constr) : int option :=
      match! r with
      | cons (<affine> ⌜_⌝) _ => Option.ret 0 
      | cons _ ?r' => (Option.map  (fun n => Int.add n 1) (count_depth r'))
      | _ => None
      end
    in
    count_depth r
  end.


Section ProtectPure.

  Definition _ProtectPure {prop:bi} (P:Prop) : prop := <affine> ⌜P⌝.
  #[global]Typeclasses Opaque _ProtectPure.

  Definition ProtectPure {prop:bi} (P:Prop) : prop := <affine> ⌜P⌝ (* transparent to diaframe, may be used in subsequent typeclass searching *) ∗
                                                      _ProtectPure P (* since we use iSteps to solve the precondition of semax_change_pre_for_forward_call,
                                                                        the pure facts obtained by iSteps will thrown away, so use _ProtectPure to keep it in SEP *).

  Lemma ProtectPure_eq {prop:bi} (P:Prop) : ProtectPure P ⊣⊢@{prop} <affine> ⌜P⌝.
  Proof. rewrite /ProtectPure /_ProtectPure. iSteps. Qed.

  Lemma extract_affine_pure_in_SEP:
    forall `{!VSTGS unit Σ} P1 P Q R,
    PROPx P (LOCALx Q (SEPx $ <affine> ⌜P1⌝::R)) ⊣⊢ PROPx (P1::P) (LOCALx Q (SEPx R)).
  Proof.
    intros.
    rewrite /PROPx /LOCALx /SEPx /= pure_and'.
    rewrite (bi.and_comm ⌜P1⌝) -bi.and_assoc; f_equiv.
    rewrite bi.and_assoc (bi.and_comm ⌜P1⌝) -bi.and_assoc; f_equiv.
    rewrite embed_sep embed_affinely embed_pure.
    iSplit; iSteps.
  Qed.

End ProtectPure.

Notation "'✋' P '🤚'" := (_ProtectPure P) (P at level 100, format "'✋' P '🤚'").

Ltac extract_nth_affine_pure_in_SEP depth :=
  rewrite (grab_nth_SEP  depth);
  rewrite extract_affine_pure_in_SEP /delete_nth //;
  apply semax_extract_PROP; intro.


(* throws exception if there is no affine pure prop in SEP *)
Ltac2 extract_affine_pures_in_SEP () :=
  unfold _ProtectPure;
  repeat
  (let _ (* make it typecheck *) := (Option.map (fun depth => let depth:constr := ltac2_int_to_gallina_int depth in
                  ltac1:(depth |- extract_nth_affine_pure_in_SEP depth) (of_constr (depth)))
                (find_depth_of_affine_in_SEP ())) in
    ()).
    
Ltac2 vstep_normalize () :=
  extract_affine_pures_in_SEP ().

(** vstep_entail *)
Ltac2 vstep_entail () := ltac1:(entailer!!).

Ltac2 is_entail () :=
  match! goal with
  | [ |- _ ⊢ _] => true
  | [ |- _] => false
  end.

Ltac2 is_call () :=
  match! goal with
  | [ |- semax _ _ _ (Scall _ _ _) _] => true
  | [ |- semax _ _ _ (Ssequence (Scall _ _ _) _) _] => true
  | [ |- semax _ _ _ (Ssequence (Ssequence (Scall _ _ _) _) _) _] => true
  | [ |- _] => false
  end.

Ltac2 is_semax_body () :=
  match! goal with
  | [ |- semax_body _ _ _ _] => true
  | [ |- _] => false
  end.
  
(** main tactics *)
Ltac2 vstep () :=
  (if is_entail () then vstep_entail ()
  else if is_call () then vstep_call ()
  else if is_semax_body () then ltac1:(start_function)
  else vstep_forward ())
  ; vstep_normalize ()
.

Ltac2 vsteps () := repeat (vstep ()).
