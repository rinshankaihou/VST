Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.

Ltac prove_cspecs_sub := split3; intros ?i; apply sub_option_get;
     repeat (constructor; [ reflexivity |]); constructor.

Ltac solve_entry H H0:=
     inv H; inv H0; first [ solve [ trivial ] | split; [ reflexivity | eexists; reflexivity] ].

Ltac LNR_tac := apply compute_list_norepet_e; reflexivity.

Ltac list_disjoint_tac := (*red; simpl; intros; contradiction.*)
     apply list_norepet_append_inv; LNR_tac.

Print  initial_world.find_id.
Check List.fold_right.
(*
Lemma suboption_Tac_Lemma {A} l1 l2:
  @List.fold_right bool (ident * A) (fun a b => if b then initial_world.find_id (fst a) l1 = Some (snd a) else false) 
                  true l2 = true -> 
  forall i (a:A),
  initial_world.find_id i l1 = Some a ->
  initial_world.find_id i l2 = Some a.
  *)

Ltac ExternsHyp_tac := first [ reflexivity | idtac ].
Ltac SC_tac := simpl; intros ? ? X H;
  repeat (destruct H; [ subst; simpl; simpl in X; try discriminate | ]);
  inv X; first [ eexists; split; [reflexivity | apply funspec_sub_refl] | idtac]; try contradiction.

Ltac HImports_tac := simpl; intros ? ? ? H1 H2;
  repeat (if_tac in H1; subst; simpl in *; try discriminate).

Ltac ImportsDef_tac := first [ reflexivity | idtac ].
Ltac ExportsDef_tac := first [ reflexivity | idtac ].
Ltac domV_tac := cbv; intros; auto.

Ltac FunctionsPreserved_tac :=
  eapply FP_entries_sound;
  [ cbv; reflexivity
  | solve [repeat (constructor; [ reflexivity | ]); constructor]
  | cbv; reflexivity
  | repeat (constructor; [ reflexivity | ]); constructor
  | cbv; reflexivity ].
Ltac FDM_tac := eapply FDM; [ cbv; reflexivity | repeat (constructor; [ cbv; reflexivity | ]); constructor].

Ltac find_id_subset_tac := simpl; intros ? ? H;
  repeat (if_tac in H; [ inv H; simpl; try reflexivity | ]); discriminate.

Ltac ComponentMerge C1 C2 :=
  eapply (ComponentJoin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C1 C2);
[ list_disjoint_tac
| list_disjoint_tac
| list_disjoint_tac
| list_disjoint_tac
| LNR_tac
| LNR_tac
| prove_cspecs_sub
| prove_cspecs_sub
| first [ find_id_subset_tac | idtac]
| first [ find_id_subset_tac | idtac]
| FDM_tac
| FunctionsPreserved_tac
| list_disjoint_tac
| list_disjoint_tac
| ExternsHyp_tac
| SC_tac
| SC_tac
| HImports_tac
(*+  HContexts. This is the side condition we'd like to exliminate - it's also
   why we need to define SubjectComponent/ObserverComponent using DEFINED
  simpl; intros.
  repeat (if_tac in H; [ inv H; inv H0 | ]). discriminate.*)
| ImportsDef_tac
| ExportsDef_tac
| LNR_tac
| LNR_tac
| domV_tac
].

Ltac VSUMerge VSU1 VSU2 :=
  eapply (VSUJoin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ VSU1 VSU2);
[ list_disjoint_tac
| list_disjoint_tac
| list_disjoint_tac
| list_disjoint_tac
| LNR_tac
| LNR_tac
| prove_cspecs_sub
| prove_cspecs_sub
| first [ find_id_subset_tac | idtac]
| first [ find_id_subset_tac | idtac]
| FDM_tac
| FunctionsPreserved_tac
| list_disjoint_tac
| list_disjoint_tac
| ExternsHyp_tac
| SC_tac
| SC_tac
| HImports_tac
(*+  HContexts. This is the side condition we'd like to exliminate - it's also
   why we need to define SubjectComponent/ObserverComponent using DEFINED
  simpl; intros.
  repeat (if_tac in H; [ inv H; inv H0 | ]). discriminate.*)
| ImportsDef_tac
| ExportsDef_tac
| LNR_tac
| LNR_tac
| domV_tac
].

Require Import VST.floyd.linking.
Require Import spec_pile_private.

Require Import verif_pile.
Definition PILE := verif_pile.PILEPRIV.

Require Import verif_onepile.
Definition ONEPILE := verif_onepile.ONEPILE PILEPRIV.

Definition onepile_pile_prog: Clight.program := 
  match link_progs pile.prog onepile.prog with
    Errors.OK p => p
  | _ => pile.prog (*arbitrary*)
  end.
Definition mrg_prog1 := ltac:
  (let x := eval hnf in onepile_pile_prog in
   let x := eval simpl in x in 
   let x := eval compute in x in 
       exact x).
Instance mrg_cs1 : compspecs. make_compspecs mrg_prog1. Defined.

Definition mrg_Vprog1:varspecs. mk_varspecs mrg_prog1. Defined.

(*unresolved imports*)
Definition mrg_Imports1:funspecs := spec_stdlib.specs.

Definition mrg_Exports1:funspecs := 
G_merge (spec_pile.PileASI PILE) (spec_onepile.OnepileASI ONEPILE).

Definition Onepile_Pile_Component:
@Component NullExtension.Espec
   mrg_Vprog1 mrg_cs1 nil mrg_Imports1 mrg_prog1 mrg_Exports1
   (G_merge (Comp_G (PileComponent))
            (Comp_G (OnepileComponent PILE))).
Proof.
  ComponentMerge PileComponent (OnepileComponent PILE).
Qed.

Definition Onepile_Pile_VSU:
@VSU NullExtension.Espec
   mrg_Vprog1 mrg_cs1 nil mrg_Imports1 mrg_prog1 mrg_Exports1.
Proof.
  VSUMerge PilePrivateVSU (OnepileVSU PILE).
Qed.

Require Import verif_apile.
Definition APILE := verif_apile.APILE PILE.

Definition apile_onepile_pile_prog: Clight.program := 
  match link_progs apile.prog mrg_prog1 with
    Errors.OK p => p
  | _ => apile.prog (*arbitrary*)
  end.
Definition mrg_prog2 := ltac:
  (let x := eval hnf in apile_onepile_pile_prog in
   let x := eval simpl in x in 
   let x := eval compute in x in 
       exact x).

Instance mrg_cs2 : compspecs. make_compspecs mrg_prog2. Defined.

Definition mrg_Vprog2:varspecs. mk_varspecs mrg_prog2. Defined.

(*unresolved imports*)
Definition mrg_Imports2:funspecs := spec_stdlib.specs.

Definition mrg_Exports2:funspecs := G_merge mrg_Exports1 (Apile_ASI PILE).

Definition Apile_Onepile_Pile_Component:
@Component NullExtension.Espec
   mrg_Vprog2 mrg_cs2 nil mrg_Imports2 mrg_prog2 mrg_Exports2
   (G_merge (Comp_G (Onepile_Pile_Component))
            (Comp_G (ApileComponent PILE))).
Proof.
  ComponentMerge (Onepile_Pile_Component) (ApileComponent PILE).
+ intuition.
Qed.

Definition Apile_Onepile_Pile_VSU:
@VSU NullExtension.Espec
   mrg_Vprog2 mrg_cs2 nil mrg_Imports2 mrg_prog2 mrg_Exports2.
Proof.
  VSUMerge (Onepile_Pile_VSU) (ApileVSU PILE).
+ intuition.
Qed.

Require Import verif_triang.

Definition triang_apile_onepile_pile_prog: Clight.program := 
  match link_progs triang.prog mrg_prog2 with
    Errors.OK p => p
  | _ => triang.prog (*arbitrary*)
  end.
Definition mrg_prog3 := ltac:
  (let x := eval hnf in triang_apile_onepile_pile_prog in
   let x := eval simpl in x in 
   let x := eval compute in x in 
       exact x).

Instance mrg_cs3 : compspecs. make_compspecs mrg_prog3. Defined.

Definition mrg_Vprog3:varspecs. mk_varspecs mrg_prog3. Defined.

(*unresolved imports*)
Definition mrg_Imports3:funspecs := spec_stdlib.specs.

Definition mrg_Exports3:funspecs := G_merge mrg_Exports2 spec_triang.TriangASI.

Definition Triang_Apile_Onepile_Pile_Component:
@Component NullExtension.Espec
   mrg_Vprog3 mrg_cs3 nil mrg_Imports3 mrg_prog3 mrg_Exports3
   (G_merge (Comp_G (Apile_Onepile_Pile_Component))
            (Comp_G (TriangComponent PILE))).
Proof.
  ComponentMerge (Apile_Onepile_Pile_Component) (TriangComponent PILE).
Qed.

Definition Triang_Apile_Onepile_Pile_VSU:
@VSU NullExtension.Espec
   mrg_Vprog3 mrg_cs3 nil mrg_Imports3 mrg_prog3 mrg_Exports3.
Proof.
  VSUMerge (Apile_Onepile_Pile_VSU) (TriangVSU PILE).
Qed.

Require Import spec_stdlib.
Require Import spec_triang.
Require Import spec_onepile.
Require Import spec_apile.
Require Import main.
Require Import spec_main.
  Lemma decreasing_inc i (I:0 <= i):
  i + 1 :: decreasing (Z.to_nat i) = decreasing (Z.to_nat (i + 1)).
  Proof. 
    replace (Z.to_nat (i+1)) with (S (Z.to_nat i)).
    unfold spec_triang.decreasing; fold spec_triang.decreasing.
    + f_equal. rewrite inj_S. rewrite Z2Nat.id by omega. omega.
    + rewrite <- Z2Nat.inj_succ by omega. f_equal; omega.
  Qed.

Require Import spec_main.
Lemma body_mainbody: semax_body mrg_Vprog3 mrg_Exports3 f_main (main_spec).
Proof.
start_function.
sep_apply (make_mem_mgr gv).
sep_apply (make_apile APILE gv).
generalize (make_onepile ONEPILE gv).
assert (change_composite_env (OnePileCompSpecs ONEPILE) (*CompSpecs*)mrg_cs3).
make_cs_preserve (OnePileCompSpecs ONEPILE) (*CompSpecs*)mrg_cs3.
change_compspecs (*CompSpecs.*)mrg_cs3.
intro Hx; sep_apply Hx; clear Hx.
forward_call gv.
forward_for_simple_bound 10
  (EX i:Z,
   PROP() LOCAL(gvars gv)
   SEP (onepile ONEPILE gv (Some (decreasing (Z.to_nat i)));
          apile APILE gv (decreasing (Z.to_nat i));
          mem_mgr gv; has_ext tt)).
-
 entailer!.
-
unfold APILE.
forward_call (i+1, decreasing(Z.to_nat i), gv).
rep_omega.
forward_call (i+1, decreasing(Z.to_nat i), gv).
rep_omega. rewrite decreasing_inc by omega.
entailer!. unfold APILE. trivial.
-
unfold APILE.
forward_call (decreasing (Z.to_nat 10), gv).
compute; split; congruence.
forward_call (decreasing (Z.to_nat 10), gv).
compute; split; congruence.
forward_call (10,gv).
omega.
forward.
Qed.

(*Alternative:*)
Definition linked_prog: Clight.program :=
 ltac: (linking.link_progs_list [ mrg_prog3; main.prog]).

Instance LinkedCompSpecs : compspecs. make_compspecs linked_prog. Defined.
Definition LinkedVprog: varspecs. mk_varspecs linked_prog. Defined.
Definition LinkedGprog: funspecs := mrg_Exports3.

Definition main_spec :=
 DECLARE _main
 WITH gv: globals
 PRE [ ] main_pre linked_prog tt gv
 POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr 0)))
    SEP(TT).

Lemma body_mainbodyALT: semax_body LinkedVprog LinkedGprog f_main (main_spec).
Proof.
start_function.
sep_apply (make_mem_mgr gv).
sep_apply (make_apile APILE gv).
generalize (make_onepile ONEPILE gv).
assert (change_composite_env (OnePileCompSpecs ONEPILE) (*CompSpecs*)LinkedCompSpecs).
make_cs_preserve (OnePileCompSpecs ONEPILE) (*CompSpecs*)LinkedCompSpecs.
change_compspecs (*CompSpecs.*)LinkedCompSpecs.
(*now necessary*) unfold onepile._pile, onepile._the_pile.
intro Hx; sep_apply Hx; clear Hx.
forward_call gv.
forward_for_simple_bound 10
  (EX i:Z,
   PROP() LOCAL(gvars gv)
   SEP (onepile ONEPILE gv (Some (decreasing (Z.to_nat i)));
          apile APILE gv (decreasing (Z.to_nat i));
          mem_mgr gv; has_ext tt)).
-
 entailer!.
-
unfold APILE.
forward_call (i+1, decreasing(Z.to_nat i), gv).
rep_omega.
forward_call (i+1, decreasing(Z.to_nat i), gv).
rep_omega. rewrite decreasing_inc by omega.
entailer!. unfold APILE. trivial.
-
unfold APILE.
forward_call (decreasing (Z.to_nat 10), gv).
compute; split; congruence.
forward_call (decreasing (Z.to_nat 10), gv).
compute; split; congruence.
forward_call (10,gv).
omega.
forward.
Qed.

Check @semax_prog. 
Lemma prog_correct x:
  @semax_prog NullExtension.Espec LinkedCompSpecs linked_prog (*tt*)x LinkedVprog LinkedGprog.
Proof.
  prove_semax_prog.
  do_semax_body_proofs (SortBodyProof.sort allmodules).
Qed.
Eval simpl in (map fst mrg_Imports3).
Print Triang_Apile_Onepile_Pile_VSU.
Require Import verif_main.

Definition triang_apile_onepile_pile_prog: Clight.program := 
  match link_progs triang.prog mrg_prog2 with
    Errors.OK p => p
  | _ => triang.prog (*arbitrary*)
  end.
Definition mrg_prog3 := ltac:
  (let x := eval hnf in triang_apile_onepile_pile_prog in
   let x := eval simpl in x in 
   let x := eval compute in x in 
       exact x).

Instance mrg_cs3 : compspecs. make_compspecs mrg_prog3. Defined.

Definition mrg_Vprog3:varspecs. mk_varspecs mrg_prog3. Defined.

(*unresolved imports*)
Definition mrg_Imports3:funspecs := spec_stdlib.specs.

Definition mrg_Exports3:funspecs := G_merge mrg_Exports2 spec_triang.TriangASI.

Definition Triang_Apile_Onepile_Pile_Component:
@Component NullExtension.Espec
   mrg_Vprog3 mrg_cs3 nil mrg_Imports3 mrg_prog3 mrg_Exports3
   (G_merge (Comp_G (Apile_Onepile_Pile_Component))
            (Comp_G (TriangComponent PILE))).
Proof.
  ComponentMerge (Apile_Onepile_Pile_Component) (TriangComponent PILE).
+ simpl; intros. if_tac in H. inv H. simpl. reflexivity.
   if_tac in H. inv H. simpl. reflexivity. discriminate.
+ simpl; intros. discriminate.
Qed
Locate PileComponent.

Definition mrg_Component:
@Component NullExtension.Espec
   mrg_Vprog mrg_cs nil mrg_Imports mrgprog mrg_Exports
   (G_merge (Comp_G (PileComponent))
            (Comp_G (OnepileComponent PILE))).
Proof. 
  eapply (ComponentJoin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
       PileComponent (OnepileComponent PILE)).
+ red; simpl; intros; contradiction.
+ red; simpl; intros. contradiction.
+ red; simpl; intros.
  destruct H; [subst | contradiction]. rename H0 into H.
  repeat (destruct H; [subst; discriminate |]). contradiction.
+ red; simpl; intros.
  destruct H; [subst | contradiction]. rename H0 into H.
  repeat (destruct H; [subst; discriminate |]). contradiction.
+ apply compute_list_norepet_e; reflexivity.
+ apply compute_list_norepet_e; reflexivity.
+ prove_cspecs_sub. 
+ prove_cspecs_sub.
+ simpl; intros. discriminate.
+ simpl; intros. if_tac in H. inv H. simpl. reflexivity. discriminate.
+ Time eapply FDM; [ cbv; reflexivity | repeat (constructor; [ cbv; reflexivity | ]); constructor]. (*1.5s*)
  (*old proof: simpl; trivial.  red; simpl; intros.
  Time (repeat (if_tac in H; [ try solve_entry H H0| clear H1])). (*12s*)
  discriminate.*)
+ (*Functions_preserved*)
  Time (eapply FP_entries_sound;
  [ cbv; reflexivity
  | solve [repeat (constructor; [ reflexivity | ]); constructor]
  | cbv; reflexivity
  | repeat (constructor; [ reflexivity | ]); constructor
  | cbv; reflexivity ]). (*2.7s*)
  (*WAS:
  Time (repeat (if_tac; [solve [subst; reflexivity] | ])). (*93s*)
  repeat (rewrite if_false by trivial).
  repeat (if_tac; [ solve [subst; first [ reflexivity | intuition] ] | ]).
  trivial.*)
+ red; simpl; intros. contradiction.
+ red; simpl; intros. contradiction.
+ reflexivity. (*merging of Ext*)
+ simpl; intros ? ? X H.
  repeat (destruct H; [ subst; simpl; simpl in X; try discriminate | ]);
  inv X; first [ eexists; split; [reflexivity | apply funspec_sub_refl] | idtac]; try contradiction.
+ simpl; intros ? ? X H.
  repeat (destruct H; [ subst; simpl; simpl in X; try discriminate | ]);
  inv X; first [ eexists; split; [reflexivity | apply funspec_sub_refl] | idtac]; try contradiction.
+ simpl; intros.
  repeat (if_tac in H; subst; simpl in *; try discriminate).
(*+  HContexts. This is the side condition we'd like to exliminate - it's also
   why we need to define SubjectComponent/ObserverComponent using DEFINED
  simpl; intros.
  repeat (if_tac in H; [ inv H; inv H0 | ]). discriminate.*)
+ reflexivity. (*forces the definition OS_imports = [spec_stdlib.free_spec'; spec_surelyMalloc.surely_malloc_numericspec]*)
+ reflexivity. (*forces the definition of OS_Exports*)
+ apply compute_list_norepet_e; reflexivity.
+ apply compute_list_norepet_e; reflexivity.
+ cbv; intros; auto.
Qed.
Definition mrg_VSU: 
  @VSU NullExtension.Espec mrg_Vprog mrg_cs nil mrg_Imports mrgprog mrg_Exports.
Proof. eexists. apply mrg_Component. Qed.

(*same nofy of proof as above*)
Definition mrg_VSU_direct: 
  @VSU NullExtension.Espec mrg_Vprog mrg_cs nil mrg_Imports mrgprog mrg_Exports.
Proof.
  eapply (VSUJoin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (PileVSU) (OnepileVSU PILE)).
+ red; simpl; intros. contradiction.
+ red; simpl; intros. contradiction.
+ red; simpl; intros.
  destruct H; [subst | contradiction]. rename H0 into H.
  repeat (destruct H; [subst; discriminate |]). contradiction.
+ red; simpl; intros.
  destruct H; [subst | contradiction]. rename H0 into H.
  repeat (destruct H; [subst; discriminate |]). contradiction.
+ apply compute_list_norepet_e; reflexivity.
+ apply compute_list_norepet_e; reflexivity.
+ prove_cspecs_sub. 
+ prove_cspecs_sub.
+ simpl; intros. discriminate.
+ simpl; intros. if_tac in H. inv H. simpl. reflexivity. discriminate.
+ Time eapply FDM; [ cbv; reflexivity | repeat (constructor; [ cbv; reflexivity | ]); constructor]. (*1.5s*)
  (*old proof: simpl; trivial.  red; simpl; intros.
  Time (repeat (if_tac in H; [ try solve_entry H H0| clear H1])). (*12s*)
  discriminate.*)
+ (*Functions_preserved*)
  Time (eapply FP_entries_sound;
  [ cbv; reflexivity
  | solve [repeat (constructor; [ reflexivity | ]); constructor]
  | cbv; reflexivity
  | repeat (constructor; [ reflexivity | ]); constructor
  | cbv; reflexivity ]). (*2.7s*)
  (*WAS:
  Time (repeat (if_tac; [solve [subst; reflexivity] | ])). (*93s*)
  repeat (rewrite if_false by trivial).
  repeat (if_tac; [ solve [subst; first [ reflexivity | intuition] ] | ]).
  trivial.*)
+ red; simpl; intros. contradiction.
+ red; simpl; intros. contradiction.
+ reflexivity. (*merging of Ext*)
+ simpl; intros ? ? X H.
  repeat (destruct H; [ subst; simpl; simpl in X; try discriminate | ]);
  inv X; first [ eexists; split; [reflexivity | apply funspec_sub_refl] | idtac]; try contradiction.
+ simpl; intros ? ? X H.
  repeat (destruct H; [ subst; simpl; simpl in X; try discriminate | ]);
  inv X; first [ eexists; split; [reflexivity | apply funspec_sub_refl] | idtac]; try contradiction.
+ simpl; intros.
  repeat (if_tac in H; subst; simpl in *; try discriminate).
(*+  HContexts. This is the side condition we'd like to exliminate - it's also
   why we need to define SubjectComponent/ObserverComponent using DEFINED
  simpl; intros.
  repeat (if_tac in H; [ inv H; inv H0 | ]). discriminate.*)
+ reflexivity. (*forces the definition OS_imports = [spec_stdlib.free_spec'; spec_surelyMalloc.surely_malloc_numericspec]*)
+ reflexivity. (*forces the definition of OS_Exports*)
+ apply compute_list_norepet_e; reflexivity.
+ apply compute_list_norepet_e; reflexivity.
+ cbv; intros; auto.
Qed.

