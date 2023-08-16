From mathcomp.ssreflect Require Import fintype ssrnat. 
Require Import Coqlib Maps Axioms Values Integers.
Require Import Blockset CUAST AST Globalenvs.
Require Import LDSim LDSimDefs Injections InjRels ValRels.
Require Import SpecLang SpecLangWDDET code.
Require Import Memdata Memperm MemAux FMemLemmas GMemory FMemory Footprint.
Local Ltac solv_eq:=
  match goal with
  | [H1: ?P , H2 : ?P |- _] => clear H1
  | [H1: ?P = _, H2: ?P = _ |- _] =>
    rewrite H1 in H2; inv H2
  | [H1: ?P = _ , H2: _ = ?P |- _] =>
    rewrite H1 in H2; inv H2
  | [H1: _ = ?P, H2: _ = ?P |- _] =>
    rewrite <- H1 in H2; inv H2
  end.

Lemma find_lock_acquire_from_ge :
  forall ge (Himp_init :ge_related ge(Genv.globalenv {|prog_defs := cu_defs lock_comp_unit; prog_public := cu_public lock_comp_unit; prog_main := 1%positive |})),
  exists fb, Genv.find_symbol ge lock_acquire_ident = Some fb /\ Genv.find_funct_ptr ge fb = Some (Internal lock_acquire_fnbody).
Proof.
  inversion 1;subst.
  specialize (H2 lock_acquire_ident).
  inversion H2; subst.
  eapply H5 in H10; eauto.
  unfold Genv.find_symbol,Genv.globalenv in *.
  simpl in *.
  ex_match2;simpl in *;subst;try discriminate.
  1-3:Esimpl;eauto;unfold Genv.find_funct_ptr,Genv.find_funct,Genv.find_def;
    rewrite<- H10; simpl; auto.
Qed.

Lemma find_lock_release_from_ge :
  forall ge (Himp_init :ge_related ge(Genv.globalenv (mkprogram (cu_defs lock_comp_unit) (cu_public lock_comp_unit) 1%positive))),
  exists fb, Genv.find_symbol ge lock_release_ident = Some fb /\ Genv.find_funct_ptr ge fb = Some (Internal lock_release_fnbody).
Proof.
  inversion 1;subst.
  specialize (H2 lock_release_ident).
  inversion H2; subst.
  eapply H5 in H10; eauto.
  all:unfold Genv.find_symbol,Genv.globalenv in *;simpl in *;
    ex_match2;simpl in *;subst;try discriminate;
        Esimpl;eauto; unfold Genv.find_funct_ptr,Genv.find_funct,Genv.find_def;
          rewrite<- H10; simpl; auto.
Qed.
Local Notation lockvar:=  (mkglobvar tt (Init_int32 Int.one :: nil) false false).
Lemma find_lock_gvar_from_ge:
  forall ge  (Himp_init :ge_related ge(Genv.globalenv (mkprogram (cu_defs lock_comp_unit) (cu_public lock_comp_unit) 1%positive))),
    exists b, Genv.find_symbol ge lock_L_ident = Some b /\ Genv.find_var_info ge b = Some lockvar.
Proof.
  inversion 1;subst.
  specialize (H2 lock_L_ident).
  inversion H2;subst.
  eapply H5 in H10;eauto.
   all:unfold Genv.find_symbol,Genv.globalenv in *;simpl in *;
     ex_match2;simpl in *;subst;try discriminate.
   unfold Genv.find_var_info,Genv.find_def;Esimpl;eauto; rewrite<- H10; simpl; auto.
Qed.
Lemma find_symb_from_ge:
   forall ge b id (Himp_init :ge_related ge(Genv.globalenv (mkprogram (cu_defs lock_comp_unit) (cu_public lock_comp_unit) 1%positive))),
     Genv.find_symbol ge id = Some b->
     id = lock_acquire_ident \/ id = lock_release_ident \/ id = lock_L_ident.
Proof.
  inversion 1;subst.
  specialize (H2 id).
  intros.
  rewrite H7 in *. inv H2.
  unfold Genv.globalenv in H8. simpl in H8.
  unfold Genv.find_symbol in H8. simpl in H8.
  destruct id;simpl in H8;auto;destruct id;simpl in H8;auto;try  destruct id;simpl in H8;try discriminate;auto.
Qed.
Lemma find_gvar_from_ge:
   forall ge b id v (Himp_init :ge_related ge(Genv.globalenv (mkprogram (cu_defs lock_comp_unit) (cu_public lock_comp_unit) 1%positive))),
     Genv.find_symbol ge id = Some b->
     Genv.find_var_info ge b = Some v->
     id = lock_L_ident /\ v = lockvar.
Proof.
  inversion 1;subst.
  specialize (H2 id). 
  intros. rewrite H7 in *. 
  unfold Genv.find_var_info in H8.
  unfold Genv.find_def in *.
  ex_match2.
  inv H8.
  apply H4 in Hx as ?.
  Hsimpl.
  inv H2.
  exploit H0. eexact H8. eexact H12. intro;subst.
  apply H5 in H8 .
  unfold Genv.globalenv in H8. simpl in H8.
  rewrite Hx in H8.
  
  destruct b0;simpl in *;try discriminate; try destruct b0;simpl in *;try discriminate;try  destruct b0;simpl in *;try discriminate.
  inv H8.
  split;auto.

  destruct id;simpl in *;try discriminate; try destruct id;simpl in *;try discriminate;try  destruct id;simpl in *;try discriminate;auto.
Qed.  
  
  
Record ge_lessmatch {F1 V1 : Type} (sge : Genv.t F1 V1) 
(tge : Genv.t F1 V1) : Prop := Build_ge_match
  { genv_public_eq : forall id : ident,
                     In id (Genv.genv_public sge) <-> In id (Genv.genv_public tge);
    genv_symb_eq_dom : forall id : positive,
                       (Genv.genv_symb sge) ! id = None <->
                       (Genv.genv_symb tge) ! id = None;
    genv_defs_match : forall (id : positive) (b b' : block),
                      (Genv.genv_symb sge) ! id = Some b ->
                      (Genv.genv_symb tge) ! id = Some b' ->
                      option_rel globdef_match (Genv.genv_defs sge) ! b
                        (Genv.genv_defs tge) ! b';}.

Lemma ge_related_ge_lessmatch{F V}:forall ge ge', @ge_related F V ge ge'->@ge_lessmatch F V ge ge'.
Proof.
  inversion 1;subst.
  constructor. split;congruence.
  intro;specialize (H3 id).
  inv H3;split;intro;try congruence;unfold Genv.find_symbol in *;try solv_eq;try congruence.
  intros.
  specialize (H3 id). inv H3;unfold Genv.find_symbol in *;solv_eq;try congruence.
  solv_eq.
  erewrite H6;eauto.
  destruct (Genv.genv_defs ge)!b eqn:?;constructor.
  destruct g;constructor.
  destruct v;constructor.
Qed.

Lemma ge_lessmatch_comm{F V}: forall x y, @ge_lessmatch F V x y -> ge_lessmatch y x.
Proof.
  destruct 1;constructor.
  split;intro;eapply genv_public_eq0;eauto.
  split;intro;eapply genv_symb_eq_dom0;eauto.
  intros. exploit genv_defs_match0;eauto.
  intro. inv H1;constructor. inv H4;constructor. inv H1;constructor.
Qed.

Lemma ge_lessmatch_trans{F V}: forall x y z,@ge_lessmatch F V x y-> ge_lessmatch y z->ge_lessmatch x z.
Proof.
  destruct 1,1.
  constructor.
  split;intro;try apply genv_public_eq0;try apply genv_public_eq1;try apply genv_public_eq0;auto.
  split;intro;try apply genv_symb_eq_dom0;try apply genv_symb_eq_dom1;try apply genv_symb_eq_dom0;auto.
  intros.
  destruct (Genv.genv_symb y)!id eqn:?.
  exploit genv_defs_match0;eauto;intro.
  exploit genv_defs_match1;eauto;intro.
  inv H1;inv H2;try congruence;try constructor;try solv_eq.
  inv H7;inv H5;try congruence;try constructor;try solv_eq.
  inv H1;inv H8;try congruence;try constructor.
  eapply genv_symb_eq_dom0 in Heqo;eauto. congruence.
Qed.
Notation cu:= lock_comp_unit.
Notation footprint := FP.t.
Notation ge:=  (Genv.globalenv  (mkprogram (cu_defs cu) (cu_public cu) 1%positive)).

Lemma lock_acquire_init_state :
  forall (tge:genv)
    (Himp_init : ge_related tge ge),
    init_core tge lock_acquire_ident nil = Some (CallStateIn (fn_body lock_acquire_fnbody)).
Proof.
  intros.
  unfold init_core.
  unfold generic_init_core.
  exploit find_lock_acquire_from_ge;eauto;intros [?[]].
  unfold fundef_init.
  ex_match2.
Qed.
Lemma lock_release_init_state :
  forall (tge:genv)
    (Himp_init : ge_related tge ge),
    init_core tge lock_release_ident nil = Some (CallStateIn (fn_body lock_release_fnbody)).
Proof.
  intros.
  unfold init_core.
  unfold generic_init_core.
  exploit find_lock_release_from_ge;eauto;intros [?[]].
  unfold fundef_init.
  ex_match2.
Qed.
Lemma lock_init_state :
  forall (tge:genv) id args
    (Himp_init : ge_related tge ge) c,
    init_core tge id args = Some c->
    args = nil /\
    (id = lock_release_ident \/ id = lock_acquire_ident).
Proof.
  unfold init_core,generic_init_core,fundef_init.
  intros.
  ex_match2. inv H;auto.
  split;auto.
  apply find_symb_from_ge in Hx as ?;auto.
  destruct H as [|[]];auto.
  subst.
  exploit find_lock_gvar_from_ge;eauto.
  intros [?[]];solv_eq.
  unfold Genv.find_funct_ptr,Genv.find_var_info in *.
  ex_match2.
Qed.
Lemma store_v_load_eq_spec_m :
  forall m m' b n,
    storemax m b (Vint n) = Some m' ->
    loadmax m' b = Some (Vint n).
Proof. 
  intros.
  unfold SpecLang.storemax in *. 
  unfold SpecLang.loadmax.
  ex_match2.
  assert(R: Mem.mem_contents m' =  PMap.set b
                              (Mem.setN (encode_val Mint32 (Vint n)) 0
                                 (Mem.mem_contents m) !! b) 
                              (Mem.mem_contents m)).
  inversion H; subst. simpl. auto.
  rewrite R. clear H.
 
  pose FMemory.Mem.getN_setN_same.
  rewrite PMap.gsspec.
  destruct peq;try contradiction.
  assert (Datatypes.length (encode_val Mint32 (Vint n)) = size_chunk_nat Mint32).
  simpl.
  unfold inj_bytes. unfold encode_int, size_chunk_nat.
  simpl.
  unfold rev_if_be.
  destruct Archi.big_endian eqn:?; try discriminate.
  eauto.
  rewrite <- H.
  rewrite Mem.getN_setN_same.
  pose proof decode_encode_val_general (Vint n) Mint32 Mint32.
  simpl in *. 
  clear - H0. 
  congruence.
  clear Hx0.
  contradict n0.
  unfold Mem.range_perm, Mem.perm in *.
  inversion H; subst.
  simpl.
  intros. exploit r;eauto.
  unfold Mem.perm_order'. ex_match2.
  intros. inv H1;constructor.
Qed.

Lemma loadmax_embed_eq:
  forall fl m m' b,
    embed (strip m) fl m'->
    loadmax m b = loadmax m' b.
Proof.
  intros.
  inv H.
  unfold loadmax.
  unfold strip in H1. inv H1.
  ex_match2.
  unfold Mem.range_perm,Mem.perm in *.
  clear Hx0;contradict n.
  intros.
  apply r in H.
  congruence.

  clear Hx;contradict n.
  unfold Mem.range_perm,Mem.perm in *.
  rewrite <- H2.
  auto.
Qed.  
Section SIMULATION.
Variable sge tge: genv.
Hypothesis SGEINIT: ge_related sge ge.
Hypothesis TGEINIT: ge_related tge ge.
Hypothesis SEQ: Genv.genv_next sge = Genv.genv_next tge.

Variable b b' b2 b2' b3 b3':block.
Hypothesis SFIND: Genv.find_symbol sge lock_L_ident = Some b.
Hypothesis TFIND: Genv.find_symbol tge lock_L_ident = Some b'.
Hypothesis SFIND2: Genv.find_symbol sge lock_acquire_ident = Some b2.
Hypothesis TFIND2: Genv.find_symbol tge lock_acquire_ident = Some b2'.
Hypothesis SFIND3: Genv.find_symbol sge lock_release_ident = Some b3.
Hypothesis TFIND3: Genv.find_symbol tge lock_release_ident = Some b3'.
Definition j (bk:block):option (block*Z):=
  if peq b bk then Some (b',0) else
    if peq b2 bk then Some (b2',0) else
      if peq b3 bk then Some (b3',0) else None.

Lemma BNEQ: b <> b2 /\ b2 <> b3 /\ b <> b3 /\ b' <> b2' /\ b2' <> b3' /\ b' <> b3'.
Proof.
  Esimpl;intro;subst.
  exploit find_lock_acquire_from_ge;try eexact SGEINIT;intros [?[]];solv_eq.
  exploit find_lock_gvar_from_ge;try eexact SGEINIT;intros [?[]];solv_eq.
  unfold Genv.find_funct_ptr,Genv.find_var_info in *;ex_match.

  exploit find_lock_acquire_from_ge;try eexact SGEINIT;intros [?[]];solv_eq.
  exploit find_lock_release_from_ge;try eexact SGEINIT;intros [?[]];solv_eq.
  unfold Genv.find_funct_ptr,Genv.find_var_info in *;ex_match;try solv_eq.

  exploit find_lock_gvar_from_ge;try eexact SGEINIT;intros [?[]];solv_eq.
  exploit find_lock_release_from_ge;try eexact SGEINIT;intros [?[]];solv_eq.
  unfold Genv.find_funct_ptr,Genv.find_var_info in *;ex_match;try solv_eq.

  exploit find_lock_acquire_from_ge;try eexact TGEINIT;intros [?[]];solv_eq.
  exploit find_lock_gvar_from_ge;try eexact TGEINIT;intros [?[]];solv_eq.
  unfold Genv.find_funct_ptr,Genv.find_var_info in *;ex_match.

  exploit find_lock_acquire_from_ge;try eexact TGEINIT;intros [?[]];solv_eq.
  exploit find_lock_release_from_ge;try eexact TGEINIT;intros [?[]];solv_eq.
  unfold Genv.find_funct_ptr,Genv.find_var_info in *;ex_match;try solv_eq.

  exploit find_lock_gvar_from_ge;try eexact TGEINIT;intros [?[]];solv_eq.
  exploit find_lock_release_from_ge;try eexact TGEINIT;intros [?[]];solv_eq.
  unfold Genv.find_funct_ptr,Genv.find_var_info in *;ex_match;try solv_eq.
Qed.
Lemma injective_j:
  forall b b' x ofs ofs', j b = Some (x,ofs) -> j b' = Some (x,ofs') -> b = b' /\ ofs = ofs' /\ ofs = 0.
Proof.
  unfold j;intros.
  pose proof BNEQ. Hsimpl.
  repeat destruct peq;inv H;inv H0;try congruence;auto.
Qed.
Lemma jb : j b = Some (b',0). unfold j;destruct peq;congruence. Qed.
Lemma jb2: j b2 = Some (b2',0). unfold j. destruct peq. pose proof BNEQ. Hsimpl. contradiction. destruct peq;try congruence. Qed.
Lemma jb3: j b3 = Some (b3',0). pose proof BNEQ;Hsimpl. unfold j;destruct peq;try congruence;destruct peq;try congruence;destruct peq;try congruence. Qed.
Lemma jbn: forall x y z, j x = Some (y,z) -> z = 0 /\ x = b \/ x = b2 \/ x = b3.
Proof. unfold j;intros;destruct peq;try congruence;try destruct peq;try congruence;try destruct peq;try congruence;auto. inv H;auto. Qed.

Record Finject f m m':=
  {
    inj: Mem.inject f m m';
    valinj: forall (b1 : block) (ofs : Z) (b2 : block) (delta : Z),
        f b1 = Some (b2, delta) ->
        Mem.perm m b1 ofs Memperm.Max Memperm.Readable ->
        memval_inject f (ZMap.get ofs (Mem.mem_contents m) !! b1)(ZMap.get (ofs+delta) ((Mem.mem_contents m')!!b2));
  }.

Record Ginject f m m':=
  {
    ginj: GMem.inject f m m';
    gvalinj: forall (b1 : block) (ofs : Z) (b2 : block) (delta : Z),
        f b1 = Some (b2, delta) ->
        GMem.perm m b1 ofs Memperm.Max Memperm.Readable ->
        memval_inject f (ZMap.get ofs (GMem.mem_contents m) !! b1)(ZMap.get (ofs+delta) ((GMem.mem_contents m')!!b2));
  }.

Lemma store_mapped_inj:
  forall f m1 b1 v1 n1 m2 b2 v2
    (VALINJ: forall (b1 : block) (ofs : Z) (b2 : block) (delta : Z),
        f b1 = Some (b2, delta) ->
        GMem.perm (strip m1) b1 ofs Memperm.Max Memperm.Readable ->
        memval_inject f (ZMap.get ofs (GMem.mem_contents (strip m1)) !! b1)(ZMap.get (ofs+delta) ((GMem.mem_contents (strip m2))!!b2))),
    GMem.mem_inj f (strip m1)(strip m2) ->
    
  storemax m1 b1 v1 = Some n1 ->
  Mem.meminj_no_overlap f m1 ->
  f b1 = Some (b2, 0) ->
  Val.inject f v1 v2 ->
  exists n2,
    storemax m2 b2 v2 = Some n2
    /\ GMem.mem_inj f (strip n1)(strip n2) /\
    forall (b1 : block) (ofs : Z) (b2 : block) (delta : Z),
      f b1 = Some (b2, delta) ->
      GMem.perm (strip n1) b1 ofs Memperm.Max Memperm.Readable ->
      memval_inject f (ZMap.get ofs (GMem.mem_contents (strip n1)) !! b1)(ZMap.get (ofs+delta) ((GMem.mem_contents (strip n2))!!b2)).
Proof.
  intros.
  assert (Mem.range_perm m2 b0 0 4 Max Writable).
  {
    unfold storemax in H0. ex_match. clear H0.
    unfold Mem.range_perm in *.
    intros. apply r in H0.
    inv H. eapply mi_perm in H2;eauto.
    assert(ofs + 0 = ofs). Lia.lia.
    rewrite H in H2. auto.
  }
  unfold storemax.
  ex_match2;try contradiction.
  eexists;split;eauto. split.
  constructor.
  { (* perm *)
    unfold storemax in H0. ex_match2. inv H0. inv H.
    unfold Mem.perm in *;simpl in *;eauto.
  }
  { (* align *)
    unfold storemax in H0. ex_match2. inv H0. inv H.
    unfold Mem.perm in *;simpl in *;eauto.
  }
(* mem_contents *)
  unfold storemax in *;ex_match2;inv H0;inv H.
  unfold Mem.perm in *;simpl in *.
  intros.
  rewrite ! PMap.gsspec.
  destruct (peq b4 b1). subst b4.
  (* block = b1, block = b2 *)
  assert (b5 = b0) by congruence. subst b5.
  assert (0 = delta) by congruence. subst delta.
  rewrite peq_true.
  apply Mem.setN_inj with (access := fun ofs => Mem.perm m1 b1 ofs Max Readable).
  apply encode_val_inject; auto.
  intros. eapply mi_memval; eauto. eauto with mem.
  destruct (peq b5 b0). subst b5.
  (* block <> b1, block = b2 *)
  rewrite Mem.setN_other. eapply mi_memval; eauto. eauto with mem.
  rewrite encode_val_length. rewrite <- size_chunk_conv. intros.
  exploit H1;eauto with mem.
  intro. destruct H6;try contradiction.
  Lia.lia.

  eapply mi_memval;eauto.

  unfold storemax in *;ex_match2;inv H0;inv H.
  unfold Mem.perm in *;simpl in *.
  intros.
  rewrite ! PMap.gsspec.
  destruct (peq b4 b1). subst b4.
  (* block = b1, block = b2 *)
  assert (b5 = b0) by congruence. subst b5.
  assert (0 = delta) by congruence. subst delta.
  rewrite peq_true.
  apply Mem.setN_inj with (access := fun ofs => Mem.perm m1 b1 ofs Max Readable).
  apply encode_val_inject; auto.
  intros. eapply VALINJ; eauto. eauto with mem.
  destruct (peq b5 b0). subst b5.
  (* block <> b1, block = b2 *)
  rewrite Mem.setN_other. eapply VALINJ; eauto. eauto with mem.
  rewrite encode_val_length. rewrite <- size_chunk_conv. intros.
  exploit H1;eauto with mem.
  intro. destruct H6;try contradiction.
  Lia.lia.

  eapply VALINJ;eauto.
Qed.
  

Lemma store_reach'':
  forall l m m' b  v ,
    storemax m b (Vint v) = Some m' ->
    (forall L b, MemClosures.reach' (strip m) l L b -> Bset.belongsto l b) ->
    forall L b,
      MemClosures.reach' (strip m') l L b->
      MemClosures.reach' (strip m) l L b.
Proof.
  induction L;intros.
  inv H1;auto. constructor;auto.
  inv H1.
  specialize (IHL _ H4).
  specialize (H0 _ _ IHL).
  unfold storemax in H.
  ex_match2.
  inv H. unfold strip in H4;simpl in H4.
  unfold GMem.perm,strip in H5;simpl in H5.
  unfold strip in H7;simpl in H7.
  econstructor;eauto.
  instantiate(1:=n).
  instantiate(1:=q).
  clear H4.
  rewrite PMap.gsspec in H7.
  ex_match2;subst;auto.

  pose proof Mem.setN_outside.
  assert (Datatypes.length (encode_val Mint32 (Vint v)) = size_chunk_nat Mint32).
  auto.
  unfold size_chunk_nat,size_chunk in H1.
  assert(Z.of_nat (length (encode_val Mint32 (Vint v))) = 4).
  rewrite H1. auto.
  clear H1.
  destruct (zlt z 0).
  rewrite H in H7;auto.

  destruct (zle 4 z).
  rewrite H in H7;auto.
  right. simpl in H2. rewrite H2. Lia.lia.

  destruct (zle 3 z).
  assert(z=3). Lia.lia. subst.
  unfold inj_bytes,encode_int,rev_if_be,bytes_of_int in H7;ex_match2;simpl in H7.
  rewrite ZMap.gss in H7;auto;try discriminate. 

  destruct (zle 2 z).
  assert(z=2). Lia.lia. subst.
  unfold inj_bytes,encode_int,rev_if_be,bytes_of_int in H7;ex_match2;simpl in H7.
  rewrite ZMap.gso in H7;[|intro R;inv R].
  rewrite ZMap.gss in H7;auto;try discriminate.

  destruct (zle 1 z).
  assert(z=1). Lia.lia. subst.
  unfold inj_bytes,encode_int,rev_if_be,bytes_of_int in H7;ex_match2;simpl in H7.
  rewrite ZMap.gso in H7;[|intro R;inv R].
  rewrite ZMap.gso in H7;[|intro R;inv R].
  rewrite ZMap.gss in H7;auto;try discriminate.

  assert(z=0). Lia.lia. subst.
  unfold inj_bytes,encode_int,rev_if_be,bytes_of_int in H7;ex_match2;simpl in H7.
  rewrite ZMap.gso in H7;[|intro R;inv R].
  rewrite ZMap.gso in H7;[|intro R;inv R].
  rewrite ZMap.gso in H7;[|intro R;inv R].
  rewrite ZMap.gss in H7;auto;try discriminate.
Qed.
Lemma store_rc:
  forall l m v b m',
    v = Vone \/ v = Vzero ->
    storemax m b v = Some m'->
    MemClosures.reach_closed (strip m) l ->
    MemClosures.reach_closed (strip m') l.
Proof.
  intros.
  inv H1.
  constructor.
  {
    assert(exists x,v = Vint x). destruct H;eauto.
    intros. inv H2.
    destruct H1;subst.
    eapply store_reach'' in H0 as ?;eauto.
    apply reachable_closure;eauto. econstructor;eauto.
    intros. apply reachable_closure;eauto.
    econstructor;eauto.
  }
  {
    unfold storemax in H0.
    ex_match.
    inv H0.
    unfold GMem.perm,strip;simpl.
    intros.
    eapply no_undef in H0;eauto.
    unfold strip in H0;simpl in H0.
    rewrite PMap.gsspec. ex_match2.
    subst b0.
    assert(exists x,v =Vint x). destruct H;eauto.
    destruct H2.
    subst v.
    simpl.
    pose proof Mem.setN_outside.
    assert (Datatypes.length (encode_val Mint32 (Vint x)) = size_chunk_nat Mint32).
    auto.
    unfold size_chunk_nat in H3. unfold size_chunk in H3.
    assert(Z.of_nat (length (encode_val Mint32 (Vint x))) = 4).
    rewrite H3. auto.
    clear H3.
    destruct (zlt z 0).
    rewrite H2;auto.

    destruct (zle 4 z).
    rewrite H2;auto.
    right. simpl in H4. rewrite H4. Lia.lia.

    destruct (zle 3 z).
    assert(z=3). Lia.lia. subst.
    unfold inj_bytes,encode_int,rev_if_be,bytes_of_int;ex_match2;simpl.
    rewrite ZMap.gss;auto. intro R;inv R.

    destruct (zle 2 z).
    assert(z=2). Lia.lia. subst.
    unfold inj_bytes,encode_int,rev_if_be,bytes_of_int;ex_match2;simpl.
    rewrite ZMap.gso;[|intro R;inv R].
    rewrite ZMap.gss;auto.
    intro R;inv R.

    destruct (zle 1 z).
    assert(z=1). Lia.lia. subst.
    unfold inj_bytes,encode_int,rev_if_be,bytes_of_int;ex_match2;simpl.
    rewrite ZMap.gso;[|intro R;inv R].
    rewrite ZMap.gso;[|intro R;inv R].
    rewrite ZMap.gss;auto.
    intro R;inv R.

    assert(z=0). Lia.lia. subst.
    unfold inj_bytes,encode_int,rev_if_be,bytes_of_int;ex_match2;simpl.
    rewrite ZMap.gso;[|intro R;inv R].
    rewrite ZMap.gso;[|intro R;inv R].
    rewrite ZMap.gso;[|intro R;inv R].
    rewrite ZMap.gss;auto.
    intro R;inv R.
  }
  {
    unfold storemax in H0.
    ex_match.
    inv H0.
    unfold GMem.perm,strip;simpl.
    intros.
    eapply no_vundef with(q:=q)(n:=n) in H0;eauto.
    unfold strip in H0;simpl in H0.
    rewrite PMap.gsspec. ex_match2.
    subst b0.
    assert(exists x,v =Vint x). destruct H;eauto.
    destruct H2.
    subst v.
    simpl.
    pose proof Mem.setN_outside.
    assert (Datatypes.length (encode_val Mint32 (Vint x)) = size_chunk_nat Mint32).
    auto.
    unfold size_chunk_nat in H3. unfold size_chunk in H3.
    assert(Z.of_nat (length (encode_val Mint32 (Vint x))) = 4).
    rewrite H3. auto.
    clear H3.
    destruct (zlt z 0).
    rewrite H2;auto.

    destruct (zle 4 z).
    rewrite H2;auto.
    right. simpl in H4. rewrite H4. Lia.lia.

    destruct (zle 3 z).
    assert(z=3). Lia.lia. subst.
    unfold inj_bytes,encode_int,rev_if_be,bytes_of_int;ex_match2;simpl.
    rewrite ZMap.gss;auto. intro R;inv R.

    destruct (zle 2 z).
    assert(z=2). Lia.lia. subst.
    unfold inj_bytes,encode_int,rev_if_be,bytes_of_int;ex_match2;simpl.
    rewrite ZMap.gso;[|intro R;inv R].
    rewrite ZMap.gss;auto.
    intro R;inv R.

    destruct (zle 1 z).
    assert(z=1). Lia.lia. subst.
    unfold inj_bytes,encode_int,rev_if_be,bytes_of_int;ex_match2;simpl.
    rewrite ZMap.gso;[|intro R;inv R].
    rewrite ZMap.gso;[|intro R;inv R].
    rewrite ZMap.gss;auto.
    intro R;inv R.

    assert(z=0). Lia.lia. subst.
    unfold inj_bytes,encode_int,rev_if_be,bytes_of_int;ex_match2;simpl.
    rewrite ZMap.gso;[|intro R;inv R].
    rewrite ZMap.gso;[|intro R;inv R].
    rewrite ZMap.gso;[|intro R;inv R].
    rewrite ZMap.gss;auto.
    intro R;inv R.
  }
Qed.
Lemma bset_inject_no_overlap:
  forall mu,
    Bset.inject (Injections.inj mu)
                (SharedSrc mu) (SharedTgt mu)->
    forall m,
      Mem.meminj_no_overlap (Bset.inj_to_meminj (Injections.inj mu)) m.
Proof.
  intros. constructor.
  inv H. inv inj_weak.
  unfold Bset.inj_to_meminj in *.
  ex_match. inv H1. inv H2.
  intro. subst.
  exploit inj_injective. eexact Hx. eexact Hx0.
  intro.
  congruence.
Qed.


Lemma store_Ginject:
  forall f m1 b1 v1 n1 m2 b2 v2,
    Ginject f (strip m1)(strip m2) ->
    storemax m1 b1 v1 = Some n1 ->
    Mem.meminj_no_overlap f m1 ->
    f b1 = Some (b2, 0) ->
    Val.inject f v1 v2 ->
    exists n2,
      storemax m2 b2 v2 = Some n2
      /\ Ginject f (strip n1)(strip n2).
Proof.
  intros.
  inv H.
  inv ginj0.
  exploit store_mapped_inj;eauto.
  intros. Hsimpl.
  Esimpl;eauto.
  econstructor;eauto.
  clear H5.
  unfold storemax in *;ex_match2.
  inv H0. inv H;simpl in *.
  econstructor;eauto.
Qed.
Lemma getN_inj:
  forall (f : meminj) (m1 m2 : mem) (b1 b2 : block) (delta : Z),
    Ginject f (strip m1)(strip m2) ->
    f b1 = Some (b2, delta) ->
    forall (n : nat) (ofs : Z),
      Mem.range_perm m1 b1 ofs (ofs + Z.of_nat n) Memperm.Max Memperm.Readable ->
      list_forall2 (memval_inject f) (Mem.getN n ofs (Mem.mem_contents m1) !! b1) (Mem.getN n (ofs+delta) (Mem.mem_contents m2) !! b2).
Proof.
  induction n; intros; simpl.
  constructor.
  rewrite inj_S in H1.
  constructor. inv H.
  eapply gvalinj0;eauto.
  unfold Mem.range_perm in H1.
  apply H1. Lia.lia.
  replace (ofs + delta + 1) with ((ofs + 1) + delta) by Lia.lia.
  apply IHn. red; intros; apply H1; Lia.lia.
Qed.

Local Notation "a # b" := (PMap.get b a) (at level 1).
Lemma loadmax_finj:
  forall f m1 m2 b1 b2 v1,
    Ginject f (strip m1)(strip m2) ->
    loadmax m1 b1 = Some v1 ->
    f b1 = Some (b2, 0) ->
    exists v2, loadmax m2 b2 = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros.
  exists (decode_val Mint32 (Mem.getN (size_chunk_nat Mint32) 0 (m2.(Mem.mem_contents)#b0))).
  split. unfold loadmax. apply pred_dec_true.
  assert(0+0=0). Lia.lia.
  assert(size_chunk Mint32 = 4 + 0). simpl. auto.
  rewrite <- H2,H3.
  inv H. inv ginj0.
  {
    unfold loadmax in H0.
    ex_match2.
    unfold Mem.range_perm in *.
    intros.
    apply r in H.
    inv mi_inj.
    unfold GMem.perm,strip in mi_perm. simpl in *.
    eapply mi_perm in H;eauto.
    assert(ofs+0=ofs). Lia.lia.
    rewrite H4 in H. auto.
  }
  unfold loadmax in H0;ex_match2.
  assert( (decode_val Mint32  (Mem.getN (size_chunk_nat Mint32) 0 (Mem.mem_contents m1) # b1)) = v1). inv H0;auto.
  rewrite<- H2.
  apply decode_val_inject.
  exploit getN_inj; eauto.
  instantiate(2:=0).
  simpl in r. instantiate(1:=4%nat). auto.
  intro. assert(0+0=0). Lia.lia.
  auto.
Qed.
Section MATCHSTATE.
  Definition st1 := Sassign r Int.zero.
  Definition st2 := Sassign x Int.zero.
  Definition bexpr1:= BEq r Int.zero.
  Definition st3:= Sloadv r lock_L_ident.
  Definition st4:= Sstorev x lock_L_ident.
  Notation " '<<' x '>>'" := (Satom x).
  Notation " x ';;' y" := (Sseq x y)  (at level 60, right associativity).
  Notation " x '--' y":= (Kseq x y)  (at level 60, right associativity).
  Definition lockfunc:=  st1;; st2;; (Swhile bexpr1 <<st3;;st4>> ) ;;Sskip.
  Variable mu:Mu.
  Hypothesis INITGE:ge_init_inj mu sge tge.
  Lemma mu_inj_b:
    Injections.inj mu b = Some b'.
  Proof.
    inv INITGE.
    specialize (senv_injected lock_L_ident).
    unfold Senv.find_symbol,Genv.to_senv in senv_injected.
    rewrite SFIND,TFIND in senv_injected.
    inv senv_injected;auto.
  Qed.
  Definition gmeminv m1 m2:=
    MemClosures.reach_closed m1 (SharedSrc mu) /\
    MemClosures.reach_closed m2 (SharedTgt mu) /\
    Ginject (Bset.inj_to_meminj (Injections.inj mu)) m1 m2.
  Lemma grange_perm_eq:
    forall f m b m2 b' p,
      Ginject f m m2->
      f b = Some (b',0)->
      GMem.range_perm m b 0 4 Max p->
      GMem.range_perm m2 b' 0 4 Max p.
  Proof.
    unfold GMem.range_perm;intros.
    inv H. inv ginj0. inv mi_inj.
    eapply mi_perm in H0;eauto.
    assert(ofs + 0 = ofs). Lia.lia.
    congruence.
  Qed.
  Lemma grange_perm_eq2:
    forall f m b m2 b' p,
      Ginject f (strip m) (strip m2)->
      f b = Some (b',0)->
      Mem.range_perm m b 0 4 Max p->
      Mem.range_perm m2 b' 0 4 Max p.
  Proof.
    unfold Mem.range_perm;intros.
    inv H. inv ginj0. inv mi_inj.
    eapply mi_perm in H0;eauto.
    unfold strip,GMem.perm in H0;simpl in H0.
    assert(ofs + 0 = ofs). Lia.lia.
    rewrite H in H0. eauto.
    unfold strip,GMem.perm;simpl;eauto.
    specialize (H1 _ H2).
    auto.
  Qed.


  Lemma store_gmeminv:
    forall m v m' m2 m2',
      gmeminv (strip m)(strip m2)->
      storemax m b v = Some m'->
      storemax m2 b' v = Some m2'->
      v = Vone \/ v = Vzero ->
      gmeminv (strip m')(strip m2').
  Proof.
    inversion INITGE.
    unfold gmeminv;intros;Hsimpl.
    pose proof bset_inject_no_overlap mu.
    pose proof mu_inj_b.
    eapply store_Ginject in H4;eauto.
    2: unfold Bset.inj_to_meminj;rewrite H6;eauto.
    2: instantiate(1:=v);destruct H2;subst;constructor.
    Hsimpl.
    solv_eq.
    eapply store_rc in H0;eauto.
    eapply store_rc in H1;eauto.
  Qed.
  Lemma gmeminv_loadmax_inj:
    forall m1 m2,
      gmeminv m1 m2 ->
      forall fl1 fm1 fl2 fm2 v,
        embed m1 fl1 fm1 ->
        embed m2 fl2 fm2 ->
        loadmax fm1 b= Some v->
        exists v', loadmax fm2 b' = Some v' /\ Val.inject (Bset.inj_to_meminj(Injections.inj mu)) v v'.
  Proof.
    intros.
    destruct H as (_&_&?).
    inv H0;inv H1.
    pose proof mu_inj_b.
    eapply loadmax_finj in H;eauto.
    unfold Bset.inj_to_meminj;rewrite H0;auto.
  Qed.
  Definition setid (te:tmp)(va:ident)(vb:val):tmp:=
    fun b => if peq b va then vb else te b.
  Definition tmp_check t:=
    exists v,  (t = setid (setid init_tmp x (Vint Int.zero)) r v).
  Definition tmp_inj (t1 t2:tmp):=
    forall id,
      val_related (Injections.inj mu) (t1 id)(t2 id).
 
  Lemma setid_comm:
    forall t v1 v2 a1 a2,
      a1 <> v1->
      setid (setid t v1 v2) a1 a2 = setid (setid t a1 a2) v1 v2.
  Proof.
    unfold setid.
    intros.
    apply functional_extensionality.
    intro. destruct peq;auto.
    subst. rewrite peq_false;auto.
  Qed.
  Lemma setid_set:
    forall t v1 v2 v3,
      setid (setid t v1 v2) v1 v3 = setid t v1 v3.
  Proof.
    unfold setid.
    intros.
    apply functional_extensionality.
    intros. destruct peq;auto.
  Qed.
  Lemma gmeminv_loadmax_rel:
    forall m1 m2 v v2,
      gmeminv (strip m1)(strip m2)->
      loadmax m1 b = Some v->
      loadmax m2 b' = Some v2 ->
      val_related (Injections.inj mu) v v2.
  Proof.
    pose proof gmeminv_loadmax_inj.
    intros.
    pose proof embed_refl m1.
    pose proof embed_refl m2.
    specialize (H (strip m1)(strip m2) H0 _ _ _ _ _ H3 H4 H1).
    Hsimpl. solv_eq.
    clear H3 H4.
    inv H5;try econstructor;eauto.
    unfold Bset.inj_to_meminj in H2.
    ex_match.
    inv H2.
    rewrite Ptrofs.add_zero.
    econstructor;eauto.

    enough(v2 = Vundef). subst. constructor.
    destruct H0 as [?[]].
    inv H3.

    pose proof mu_inj_b as mub.
    assert(Shardb: Bset.belongsto (SharedSrc mu) b).
    inv INITGE.
    apply mu_inject in mub;auto.
    unfold loadmax in *.
    ex_match.
    unfold size_chunk_nat,size_chunk in *.
    assert(Z.to_nat 4=4%nat). auto.
    rewrite H3 in *. clear H3.
    unfold strip,GMem.perm in gvalinj0;simpl in gvalinj0.
    assert(decode_val Mint32 (Mem.getN 4 0 (Mem.mem_contents m2) # b') = v2).
    inv H;auto.
    rewrite <- H3. clear H H3.
    assert(decode_val Mint32 (Mem.getN 4 0 (Mem.mem_contents m1) # b ) = Vundef).
    inv H1;auto.
    clear H1.
    assert(valinj:
             forall ofs,
               0<= ofs < 4 ->
               memval_inject (Bset.inj_to_meminj(Injections.inj mu))
                             (ZMap.get ofs (Mem.mem_contents m1) # b)
                             (ZMap.get ofs (Mem.mem_contents m2) # b')).
    {
      intros.
      exploit gvalinj0.
      unfold Bset.inj_to_meminj. rewrite mub. eauto.
      instantiate(1:=ofs). apply r;auto.
      intro.
      assert(ofs + 0 = ofs). Lia.lia.
      congruence.
    }
    clear gvalinj0.
    assert(val_noundef:
             forall ofs,
               0<= ofs <4->
               ZMap.get ofs (Mem.mem_contents m1) # b <> Undef).
    intros.
    inv H0. apply no_undef;auto.
    unfold GMem.perm,strip;simpl;eauto.
    eapply r;eauto.
    assert(valfrag_noundef:
             forall ofs q n,
               0<= ofs <4->
               ZMap.get ofs (Mem.mem_contents m1) # b <> Fragment Vundef q n).
    intros. inv H0. apply no_vundef;auto.
    unfold GMem.perm,strip;simpl;eauto.
    eapply r;eauto.
    Ltac extract_byte:=
      match goal with
        H: context[match ZMap.get ?x (Mem.mem_contents ?m) # ?b with _ => _ end] |- _ => destruct (ZMap.get x (Mem.mem_contents m) # b) eqn:? end.
    Ltac valundef:=
      match goal with
        H:forall ofs : Z,
          0 <= ofs < 4 -> ZMap.get ofs (Mem.mem_contents ?m) # ?b <> Undef |- _=>
        exploit H;eauto;try Lia.lia
      end.
    unfold decode_val in *.
    ex_match.
    assert(proj_bytes (Mem.getN 4 0 (Mem.mem_contents m2) # b') = None).
    {
      simpl in Hx1.
      extract_byte;[valundef| |].
      Focus 2.
      exploit valinj. instantiate(1:=0). Lia.lia.
      intro. rewrite Heqm in H1. inv H1; simpl.
      rewrite <- H7. auto.

      extract_byte;[valundef| |].
      Focus 2.
      exploit valinj. instantiate(1:=1). Lia.lia.
      intro. rewrite Heqm0 in H1. inv H1; simpl.
      rewrite <-H7. ex_match2;auto.

      extract_byte;[valundef| |].
      Focus 2.
      exploit valinj. instantiate(1:=2). Lia.lia.
      intro. rewrite Heqm1 in H1. inv H1; simpl.
      rewrite <-H7. ex_match2;auto.

      extract_byte;[valundef| |].
      Focus 2.
      exploit valinj. instantiate(1:=3). Lia.lia.
      intro. rewrite Heqm2 in H1. inv H1; simpl.
      rewrite <-H7. ex_match2;auto.
      congruence.
    }

    rewrite H1.
    unfold Val.load_result in *.
    destruct Archi.ptr64;try discriminate.

    unfold Mem.getN in *.
    unfold proj_value in *.
    extract_byte;[valundef| |].
    exploit valinj. instantiate(1:=0). Lia.lia.
    intro. rewrite Heqm in H3. inv H3. auto.

    exploit valinj. instantiate(1:=0). Lia.lia.
    intro. rewrite Heqm in H3. inv H3.
     
    destruct check_value eqn:?.
    {
      enough(check_value (size_quantity_nat Q32) v0 Q32   (Fragment v0 q n
         :: ZMap.get (0 + 1) (Mem.mem_contents m2) # b'
            :: ZMap.get (0 + 1 + 1) (Mem.mem_contents m2) # b'
            :: ZMap.get (0 + 1 + 1 + 1) (Mem.mem_contents m2) # b' :: nil) = true).
      rewrite H3.
      inv H5;inv H;auto.
      inv H0.
      exploit no_vundef;eauto.
      unfold strip,GMem.perm;simpl. apply r;Lia.lia.
      intro;contradiction.
      assert(novundef0:v <> Vundef).
      inv H0. intro;subst.
      exploit no_vundef;eauto.
      unfold strip,GMem.perm;simpl;apply r;auto. Lia.lia.
      clear H H1.
      simpl in *.
      Ltac andb_split:=
        repeat match goal with
               |H: _ && _ = true |- _ => apply andb_true_iff in H as []
               end;
        repeat match goal with
               |H: _ |- _ && _ = true => apply andb_true_iff;split;auto
               end;
        try match goal with
        | H :_ |- Val.eq ?x ?x = true => destruct (Val.eq x x) eqn:?;try discriminate;auto
        end.
      andb_split.
      destruct (Val.eq v0 v0);try discriminate;auto.
      ex_match.
      andb_split.
      destruct (Val.eq v v1) eqn:?;try discriminate;subst.
      exploit valinj. instantiate(1:=1). Lia.lia.
      intro. rewrite Hx3 in H10. inv H10.
      andb_split.
      {
        inv H5;inv H12;auto.
        rewrite H10 in H13;inv H13;auto.
        destruct (  Val.eq (Vptr b5 (Ptrofs.add ofs1 (Ptrofs.repr delta0)))
                           (Vptr b5 (Ptrofs.add ofs1 (Ptrofs.repr delta0)))) eqn:?;try discriminate;auto.
      }
      ex_match;andb_split.
      destruct (Val.eq v1 v) eqn:?;try discriminate;subst.
      exploit valinj. instantiate(1:=2). Lia.lia.
      intro. rewrite Hx4 in H14. inv H14.
      andb_split.
      {
        inv H5;inv H17;auto.
        rewrite H14 in H18;inv H18;auto.
        destruct ( Val.eq (Vptr b5 (Ptrofs.add ofs1 (Ptrofs.repr delta0)))
                          (Vptr b5 (Ptrofs.add ofs1 (Ptrofs.repr delta0)))) eqn:?;try discriminate;auto.
      }
      ex_match;andb_split.
      destruct (Val.eq v v1) eqn:?;try discriminate;subst.
      exploit valinj. instantiate(1:=3). Lia.lia.
      intro. rewrite Hx5 in H19. inv H19.
      andb_split.

      inv H5;inv H22;auto.
      rewrite H19 in H23;inv H23;auto.
      destruct ( Val.eq (Vptr b5 (Ptrofs.add ofs1 (Ptrofs.repr delta0)))
                        (Vptr b5 (Ptrofs.add ofs1 (Ptrofs.repr delta0)))) eqn:?;try discriminate;auto.
    }
    {
      assert(  inj_injective : forall b1 b2 b' : block,
                Injections.inj mu b1 = Some b' ->
                Injections.inj mu b2 = Some b' -> b1 = b2).
      inv INITGE.
      inv mu_inject.
      inv inj_weak. auto.
      enough(check_value (size_quantity_nat Q32) v0 Q32
        (Fragment v0 q n
         :: ZMap.get (0 + 1) (Mem.mem_contents m2) # b'
            :: ZMap.get (0 + 1 + 1) (Mem.mem_contents m2) # b'
            :: ZMap.get (0 + 1 + 1 + 1) (Mem.mem_contents m2) # b' :: nil) = false).
      rewrite H3;auto.

      clear H H1.
      assert(novundef0:v <> Vundef).
      inv H0. intro;subst.
      exploit no_vundef;eauto.
      unfold strip,GMem.perm;simpl;apply r;auto. Lia.lia.
      Ltac andb_false_split:=
        repeat match goal with
               |H: _ && _ = false |- _ => apply andb_false_iff in H as [|]
               end.
      simpl in *.
      andb_false_split.
      destruct (Val.eq v v) eqn:?;try discriminate;try contradiction.
      apply andb_false_iff;left;apply andb_false_iff;left;apply andb_false_iff;right;auto.
      apply andb_false_iff;left;apply andb_false_iff;right;auto.
      apply andb_false_iff;right.

      exploit valinj. instantiate(1:=1). Lia.lia.
      intro.
      ex_match.
      valundef.
      inv H1. auto.
      inv H1.

      andb_false_split.
      apply andb_false_iff;left;apply andb_false_iff;left;apply andb_false_iff;left.
      destruct (Val.eq v v1);try discriminate.
      assert(v1 <> Vundef).
      intro;subst.
      exploit valfrag_noundef;eauto. Lia.lia.
      destruct (Val.eq v0 v4);try discriminate;auto.
      subst. inv H5;inv H4;try congruence.
      unfold Bset.inj_to_meminj in *. ex_match. inv H3;inv H10.
   
      eapply inj_injective in Hx4;try apply Hx5;auto. subst.
      do 2 rewrite Ptrofs.add_zero in H11. subst.
      contradiction.
      apply andb_false_iff;left;apply andb_false_iff;left;apply andb_false_iff;right;auto.
      apply andb_false_iff;left;apply andb_false_iff;right;auto.
      apply andb_false_iff;right.
      exploit valinj. instantiate(1:=2). Lia.lia.
      intro.
      ex_match.
      valundef.
      inv H1. auto.
      inv H1.

      andb_false_split.
      apply andb_false_iff;left;apply andb_false_iff;left;apply andb_false_iff;left.
      destruct (Val.eq v v3);try discriminate.
      assert(v3 <> Vundef).
      intro;subst.
      exploit valfrag_noundef;eauto. Lia.lia.
      destruct (Val.eq v0 v6);try discriminate;auto.
      subst. inv H5;inv H6;try congruence.
      unfold Bset.inj_to_meminj in *. ex_match. inv H3;inv H12.

      eapply inj_injective in Hx5;try apply Hx6;auto. subst.
      do 2 rewrite Ptrofs.add_zero in H13. subst.
      contradiction.
      apply andb_false_iff;left;apply andb_false_iff;left;apply andb_false_iff;right;auto.
      apply andb_false_iff;left;apply andb_false_iff;right;auto.
      apply andb_false_iff;right.
      exploit valinj. instantiate(1:=3). Lia.lia.
      intro.
      ex_match.
      valundef.
      inv H1. auto.
      inv H1.

      andb_false_split.
      apply andb_false_iff;left;apply andb_false_iff;left;apply andb_false_iff;left.
      destruct (Val.eq v v5);try discriminate.
      assert(v5 <> Vundef).
      intro;subst.
      exploit valfrag_noundef;eauto. Lia.lia.
      destruct (Val.eq v0 v8);try discriminate;auto.
      subst. inv H5;inv H7;try congruence.
      unfold Bset.inj_to_meminj in *. ex_match. inv H3;inv H14.

      eapply inj_injective in Hx6;try apply Hx7;auto. subst.
      do 2 rewrite Ptrofs.add_zero in H15. subst.
      contradiction.
      apply andb_false_iff;left;apply andb_false_iff;left;apply andb_false_iff;right;auto.
      apply andb_false_iff;left;apply andb_false_iff;right;auto.
      apply andb_false_iff;right;auto.
    }
Qed.

  Inductive match_lock : core->gmem->core->gmem->Prop:=
  | match_callinl:
      forall sm tm,
        gmeminv sm tm->
        match_lock (CallStateIn (lockfunc;;Sskip)) sm (CallStateIn (lockfunc;;Sskip) ) tm
  | match_begin:
      forall sm tm,
        gmeminv sm tm->
        match_lock (State (lockfunc;;Sskip) Kstop init_tmp) sm (State (lockfunc;;Sskip) Kstop init_tmp) tm
  | match_1:
      forall sm tm,
        gmeminv sm tm->
        match_lock (State lockfunc (Sskip--Kstop) init_tmp) sm (State lockfunc (Sskip--Kstop) init_tmp) tm
  | match_2:
      forall sm tm,
        gmeminv sm tm->
        match_lock (State st1 ((st2;;(Swhile bexpr1 <<st3;;st4>>);;Sskip)--Sskip--Kstop) init_tmp) sm  (State st1 ((st2;;(Swhile bexpr1 <<st3;;st4>>);;Sskip)--Sskip--Kstop) init_tmp) tm
  | match_3:
      forall sm tm,
        gmeminv sm tm->
        match_lock (State Sskip ((st2;;(Swhile bexpr1 <<st3;;st4>>);;Sskip)--Sskip--Kstop) (setid init_tmp r Vzero)) sm  (State Sskip ((st2;;(Swhile bexpr1 <<st3;;st4>>);;Sskip)--Sskip--Kstop) (setid init_tmp r Vzero)) tm
  | match_4:
      forall sm tm,
        gmeminv sm tm->
        match_lock (State (st2;;(Swhile bexpr1 <<st3;;st4>>);;Sskip) (Sskip--Kstop) (setid init_tmp r Vzero)) sm  (State (st2;;(Swhile bexpr1 <<st3;;st4>>);;Sskip) (Sskip--Kstop) (setid init_tmp r Vzero)) tm
  | match_5:
      forall sm tm,
        gmeminv sm tm->
        match_lock (State st2 (((Swhile bexpr1 <<st3;;st4>>);;Sskip)--Sskip--Kstop)(setid init_tmp r Vzero)) sm (State st2 (((Swhile bexpr1 <<st3;;st4>>);;Sskip)--Sskip--Kstop)(setid init_tmp r Vzero)) tm
  | match_6:
      forall sm tm,
        gmeminv sm tm->
        match_lock (State Sskip (((Swhile bexpr1 <<st3;;st4>>);;Sskip)--Sskip--Kstop)(setid (setid init_tmp r Vzero) x Vzero)) sm (State Sskip (((Swhile bexpr1 <<st3;;st4>>);;Sskip)--Sskip--Kstop)(setid (setid init_tmp r Vzero) x Vzero)) tm
  | match_7:
      forall sm tm,
        gmeminv sm tm->
        match_lock (State ((Swhile bexpr1 <<st3;;st4>>);;Sskip) (Sskip--Kstop)(setid (setid init_tmp r Vzero) x Vzero)) sm (State ((Swhile bexpr1 <<st3;;st4>>);;Sskip) (Sskip--Kstop)(setid (setid init_tmp r Vzero) x Vzero)) tm
  | match_7_1:
      forall sm tm t1 t2,
        gmeminv sm tm->
        tmp_check t1->
        tmp_check t2->
        tmp_inj t1 t2->
        match_lock (State (Swhile bexpr1 <<st3;;st4>>) (Sskip--Sskip--Kstop) t1) sm (State (Swhile bexpr1 <<st3;;st4>>) (Sskip--Sskip--Kstop)t2) tm
  | match_8:
      forall sm tm t1 t2,
        gmeminv sm tm->
        tmp_check t1->
        tmp_check t2->
        tmp_inj t1 t2->
        match_lock (State <<st3;;st4>> ((Swhile bexpr1 <<st3;;st4>>)--Sskip--Sskip--Kstop)t1) sm (State <<st3;;st4>>((Swhile bexpr1 <<st3;;st4>>)--Sskip--Sskip--Kstop)t2) tm
  | match_9:
      forall sm tm t1 t2,
        gmeminv sm tm->
        tmp_check t1->
        tmp_check t2->
        tmp_inj t1 t2->
        match_lock (EntAtomState (st3;;st4) ((Swhile bexpr1 <<st3;;st4>>)--Sskip--Sskip--Kstop)t1) sm (EntAtomState (st3;;st4)((Swhile bexpr1 <<st3;;st4>>)--Sskip--Sskip--Kstop)t2) tm
  | match_10:
      forall sm tm t1 t2,
        gmeminv sm tm->
        tmp_check t1->
        tmp_check t2->
        tmp_inj t1 t2->
        match_lock (AtomState (st3;;st4) Kstop ((Swhile bexpr1 <<st3;;st4>>)--Sskip--Sskip--Kstop)t1) sm (AtomState (st3;;st4) Kstop ((Swhile bexpr1 <<st3;;st4>>)--Sskip--Sskip--Kstop)t2) tm
  | match_11:
      forall sm tm t1 t2,
        gmeminv sm tm->
        tmp_check t1->
        tmp_check t2->
        tmp_inj t1 t2->
        match_lock (AtomState st3 (st4--Kstop) ((Swhile bexpr1 <<st3;;st4>>)--Sskip--Sskip--Kstop)t1) sm (AtomState st3(st4--Kstop) ((Swhile bexpr1 <<st3;;st4>>)--Sskip--Sskip--Kstop)t2) tm
  | match_12:
      forall sm tm t1 t2,
        gmeminv sm tm->
        tmp_check t1->
        tmp_check t2->
        tmp_inj t1 t2->
        match_lock (AtomState Sskip (st4--Kstop) ((Swhile bexpr1 <<st3;;st4>>)--Sskip--Sskip--Kstop) t1) sm (AtomState Sskip (st4--Kstop) ((Swhile bexpr1 <<st3;;st4>>)--Sskip--Sskip--Kstop)t2) tm
  | match_13:
      forall sm tm t1 t2,
        gmeminv sm tm->
        tmp_check t1->
        tmp_check t2->
        tmp_inj t1 t2->
        match_lock (AtomState st4 Kstop  ((Swhile bexpr1 <<st3;;st4>>)--Sskip--Sskip--Kstop) t1) sm (AtomState st4 Kstop ((Swhile bexpr1 <<st3;;st4>>)--Sskip--Sskip--Kstop)t2) tm
  | match_14:
      forall sm tm t1 t2,
        gmeminv sm tm->
        tmp_check t1->
        tmp_check t2->
        tmp_inj t1 t2->
        match_lock (AtomState Sskip Kstop ((Swhile bexpr1 <<st3;;st4>>)--Sskip--Sskip--Kstop) t1) sm  (AtomState Sskip Kstop ((Swhile bexpr1 <<st3;;st4>>)--Sskip--Sskip--Kstop) t2) tm
  | match_15:
      forall sm tm t1 t2,
        gmeminv sm tm->
        tmp_check t1->
        tmp_check t2->
        tmp_inj t1 t2->
        match_lock (ExtAtomState ((Swhile bexpr1 <<st3;;st4>>)--Sskip--Sskip--Kstop) t1) sm  (ExtAtomState ((Swhile bexpr1 <<st3;;st4>>)--Sskip--Sskip--Kstop) t2) tm
  | match_16:
      forall sm tm t1 t2,
        gmeminv sm tm->
        tmp_check t1->
        tmp_check t2->
        tmp_inj t1 t2->
        match_lock (State Sskip ((Swhile bexpr1 <<st3;;st4>>)--Sskip--Sskip--Kstop) t1) sm  (State Sskip ((Swhile bexpr1 <<st3;;st4>>)--Sskip--Sskip--Kstop) t2) tm
  | match_17:
      forall sm tm t1 t2,
        gmeminv sm tm->
        tmp_check t1->
        tmp_check t2->
        tmp_inj t1 t2->
        match_lock (State (Swhile bexpr1 <<st3;;st4>>) (Sskip--Sskip--Kstop) t1) sm  (State (Swhile bexpr1 <<st3;;st4>>)(Sskip--Sskip--Kstop) t2) tm
  | match_18:
      forall sm tm t1 t2,
        gmeminv sm tm->
        tmp_check t1->
        tmp_check t2->
        tmp_inj t1 t2->
        match_lock (State Sskip (Sskip--Sskip--Kstop) t1) sm  (State Sskip (Sskip--Sskip--Kstop) t2) tm
  | match_19:
      forall sm tm t1 t2,
        gmeminv sm tm->
        tmp_check t1->
        tmp_check t2->
        tmp_inj t1 t2->
        match_lock (State Sskip (Sskip--Kstop) t1) sm (State Sskip (Sskip--Kstop) t2) tm
  | match_20:
      forall sm tm t1 t2,
        gmeminv sm tm->
        tmp_check t1->
        tmp_check t2->
        tmp_inj t1 t2->
        match_lock (State Sskip Kstop t1) sm (State Sskip Kstop t2) tm. 

  Lemma match_lock_match_mem:
    forall m c m' c',
      match_lock c m c' m'->
      gmeminv m m'.
  Proof. inversion 1;subst;auto. Qed.
  Lemma inj_init_tmp:  tmp_inj init_tmp init_tmp.
  Proof. constructor. Qed.
  Lemma setid_inj:
    forall t t' v v' b,
      tmp_inj t t'->
      val_related (Injections.inj mu) v v'->
      tmp_inj (setid t b v)(setid t' b v').
  Proof. unfold tmp_inj; intros. unfold setid;ex_match2; eauto. Qed.

  Hint Resolve inj_init_tmp setid_inj setid_comm setid_set : tmpls.
  
  Lemma match_lock_eq:
    forall m s k te m' s' k' te',
      match_lock (State s k te) m (State s' k' te') m'->
      s = s' /\ k = k' /\ tmp_inj te te'.
  Proof.
    inversion 1;subst;Esimpl;eauto with tmpls;    eapply setid_inj;eauto with tmpls;try constructor;eapply setid_inj;eauto with tmpls;constructor.
  Qed.
  Lemma match_lock_eq2:
    forall m s k te m' sc,
      match_lock (State s k te) m sc m'->
      exists te',sc = State s k te' /\ tmp_inj te te'.
  Proof.
    inversion 1;subst;Esimpl;eauto with tmpls;    eapply setid_inj;eauto with tmpls;try constructor;eapply setid_inj;eauto with tmpls;constructor.
  Qed.
  Lemma match_lock_eq3:
    forall m s k te m' s' k' te' k2 k2',
      match_lock (AtomState s k k2 te) m (AtomState s' k' k2' te') m'->
      s = s' /\ k = k' /\ k2 = k2' /\ tmp_inj te te'.
  Proof.
    inversion 1;subst;Esimpl;eauto with tmpls;    eapply setid_inj;eauto with tmpls;try constructor;eapply setid_inj;eauto with tmpls;constructor.
  Qed.
  Lemma match_lock_eq4:
    forall m s k k2 te m' sc,
      match_lock (AtomState s k k2 te) m sc m'->
      exists te',sc = AtomState s k k2 te' /\ tmp_inj te te'.
  Proof.
    inversion 1;subst;Esimpl;eauto with tmpls;    eapply setid_inj;eauto with tmpls;try constructor;eapply setid_inj;eauto with tmpls;constructor.
  Qed.
  Lemma setid_i:
    forall te b v, (setid te b v) b =v .
  Proof.
    unfold setid;intros;ex_match2.
  Qed.
  Lemma match_normal_step_lock:
  forall sfp  s k te m s' k' te' m' ,
    normalstep sge s k te m sfp s' k' te' m'->
    forall s2 k2 te2 tm,
      match_lock (State s k te) (strip m) (State s2 k2 te2) (strip tm) ->
      exists tfp tm' te2' ,
        normalstep tge s2 k2 te2 tm tfp s' k' te2' tm'/\
        match_lock (State s' k' te') (strip m') (State s' k' te2') (strip tm').
  Proof.
    intros.
    inv H0;inv H.
    all: try(Esimpl;eauto; econstructor;eauto;fail).
    {
      Esimpl;eauto;econstructor;eauto.
      unfold tmp_check. exists Vzero.
      rewrite setid_comm. unfold Vzero;auto;split;auto. intro;discriminate.
      unfold tmp_check. exists Vzero.
      rewrite setid_comm. unfold Vzero;auto;split;auto. intro;discriminate.
      eapply setid_inj;eauto;try eapply setid_inj;eauto;constructor.
    }
    {
      Esimpl;eauto;econstructor;eauto.
      inv H14. econstructor;eauto.
      specialize (H12 r).
      rewrite H0 in H12. inv H12;auto.
    }
    {
      inv H14. specialize (H12 r) as R.
      pose proof H10 as ?. pose proof H11 as ?.
      unfold tmp_check in H,H1.
      Hsimpl.
      assert(te' r = x0).
      rewrite H,setid_i;auto.
      assert(te2 r<> Vint Int.zero).
      inv R;try congruence.
      Esimpl;eauto;econstructor;eauto.
      constructor;auto.
    }
    {
      Esimpl;eauto;econstructor;eauto.
      inv H14. specialize (H12 r).
      constructor. inv H12;try congruence.
    }
    {
      Esimpl;eauto;econstructor;eauto.
      inv H14. specialize (H12 r) as R.
      pose proof H10 as ?. pose proof H11 as ?.
      unfold tmp_check in H,H1.
      Hsimpl.
      assert(te' r = x0).
      rewrite H,setid_i;auto.
      constructor.
      inv R;try congruence.
    }
  Qed.

  Lemma match_atomic_step_lock:
  forall sfp  s k te m s' k' te' m' ,
    normalstep sge s k te m sfp s' k' te' m'->
    forall s2 k2 te2 tm k0 k3,
      match_lock (AtomState s k k0 te) (strip m) (AtomState s2 k2 k3 te2) (strip tm) ->
      exists tfp tm' te2' ,
        normalstep tge s2 k2 te2 tm tfp s' k' te2' tm'/\
        match_lock (AtomState s' k' k0 te') (strip m') (AtomState s' k' k3 te2') (strip tm').
  Proof.
    intros.
    inv H0;inv H.
    all: try (Esimpl;eauto;econstructor;eauto;fail).
    {
      rewrite SFIND in H2. inversion H2;clear H2;subst b0.
      pose proof H3 as R.
      unfold loadmax in R. ex_match. 
      exploit gmeminv_loadmax_inj;eauto.
      econstructor;eauto. econstructor;eauto.
      intros [?[]].
      Esimpl;eauto. econstructor;eauto. reflexivity.
      econstructor;eauto.
      unfold tmp_check. unfold tmp_check in H12.
      Hsimpl.
      rewrite H1.
      exists v. unfold setid. 
      apply functional_extensionality;intro;ex_match2.
      unfold tmp_check. unfold tmp_check in H13.
      Hsimpl. rewrite H1.  
      exists x. unfold setid. 
      apply functional_extensionality;intro;ex_match2.
      apply setid_inj;auto.
      exploit gmeminv_loadmax_rel;eauto.
    }
    {
      rewrite SFIND in H2. inversion H2;clear H2; subst b0.
      assert(exists tm', storemax tm b' (te2 x) = Some tm').
      unfold storemax in *.
      ex_match2.
      Esimpl;eauto.
      clear Hx0. contradict n.
      inv H11. Hsimpl.
      eapply grange_perm_eq2;eauto.
      unfold Bset.inj_to_meminj. rewrite mu_inj_b. auto.
      Hsimpl.
      pose proof H12 as R1.
      pose proof H13 as R2.
      unfold tmp_check in H12,H13.
      Hsimpl.
      rewrite H1,setid_comm,setid_i in H4;try (intro;discriminate;fail).
      rewrite H0,setid_comm,setid_i in H;try(intro;discriminate).
      eapply store_gmeminv in H11;eauto.
      Esimpl;eauto;econstructor;eauto.
      rewrite H0,setid_comm,setid_i;try (intro;discriminate);auto.
    }
  Qed.
  Definition stx:= Sassign x Int.one.
  Definition sta:=Sassert bexpr1.
  Definition unlockfunc:= <<st3;;stx;;sta;;st4 >>.
  Definition tmp_check2 t:=
    exists v,  (t = setid (setid init_tmp x (Vint Int.one)) r v).
  Inductive match_unlock:core->gmem->core->gmem->Prop:=
  | match_callin:
      forall sm tm,
        gmeminv sm tm->
        match_unlock (CallStateIn (unlockfunc;;Sskip)) sm
                     (CallStateIn (unlockfunc;;Sskip)) tm
  | match_beginu:
      forall sm tm,
        gmeminv sm tm->
        match_unlock (State (unlockfunc;;Sskip) Kstop init_tmp) sm
                     (State (unlockfunc;;Sskip) Kstop init_tmp) tm
  | match_1':
      forall sm tm,
        gmeminv sm tm->
        match_unlock (State unlockfunc (Sskip--Kstop) init_tmp) sm
                     (State unlockfunc (Sskip--Kstop) init_tmp) tm
  | match_2':
      forall sm tm,
        gmeminv sm tm->
        match_unlock (EntAtomState (st3;;stx;;sta;;st4) (Sskip--Kstop) init_tmp) sm
                     (EntAtomState (st3;;stx;;sta;;st4)(Sskip--Kstop) init_tmp) tm
  | match_3':
      forall sm tm,
        gmeminv sm tm->
        match_unlock (AtomState (st3;;stx;;sta;;st4) Kstop (Sskip--Kstop) init_tmp)sm
                     (AtomState (st3;;stx;;sta;;st4) Kstop (Sskip--Kstop) init_tmp)tm
  | match_4':
      forall sm tm,
        gmeminv sm tm->
        match_unlock (AtomState st3 ((stx;;sta;;st4)--Kstop) (Sskip--Kstop) init_tmp)sm
                     (AtomState st3 ((stx;;sta;;st4)--Kstop) (Sskip--Kstop) init_tmp)tm
  | match_5':
      forall sm tm t t2,
        gmeminv sm tm->
        (exists v,t = setid init_tmp r v ) ->
        (exists v,t2 = setid init_tmp r v ) ->
        tmp_inj t t2->
        match_unlock (AtomState Sskip ((stx;;sta;;st4)--Kstop) (Sskip--Kstop) t) sm
                     (AtomState Sskip ((stx;;sta;;st4)--Kstop) (Sskip--Kstop) t2) tm
  | match_6':
      forall sm tm t t2,
        gmeminv sm tm->
        (exists v,t = setid init_tmp r v ) ->
        (exists v,t2 = setid init_tmp r v ) ->
        tmp_inj t t2->
        match_unlock (AtomState (stx;;sta;;st4) Kstop (Sskip--Kstop) t) sm
                     (AtomState (stx;;sta;;st4) Kstop (Sskip--Kstop) t2) tm
  | match_7':
      forall sm tm t t2,
        gmeminv sm tm->
        (exists v,t = setid init_tmp r v ) ->
        (exists v,t2 = setid init_tmp r v ) ->
        tmp_inj t t2->
        match_unlock (AtomState stx ((sta;;st4)--Kstop) (Sskip--Kstop) t) sm
                     (AtomState stx ((sta;;st4)--Kstop) (Sskip--Kstop) t2) tm
  | match_8':
      forall sm tm t t2,
        gmeminv sm tm->
        tmp_check2 t ->
        tmp_check2 t2->
        tmp_inj t t2->
        match_unlock (AtomState Sskip ((sta;;st4)--Kstop) (Sskip--Kstop) t) sm
                     (AtomState Sskip ((sta;;st4)--Kstop) (Sskip--Kstop) t2) tm
  | match_9':
      forall sm tm t t2,
        gmeminv sm tm->
        tmp_check2 t ->
        tmp_check2 t2->
        tmp_inj t t2->
        match_unlock (AtomState (sta;;st4) Kstop (Sskip--Kstop) t) sm
                     (AtomState (sta;;st4) Kstop (Sskip--Kstop) t2) tm
  | match_10':
      forall sm tm t t2,
        gmeminv sm tm->
        tmp_check2 t ->
        tmp_check2 t2->
        tmp_inj t t2->
        match_unlock (AtomState sta (st4--Kstop) (Sskip--Kstop) t) sm
                     (AtomState sta (st4--Kstop) (Sskip--Kstop) t2) tm
  | match_11':
      forall sm tm t,
        gmeminv sm tm->
        t = setid (setid init_tmp r Vzero) x Vone ->
        match_unlock (AtomState Sskip (st4--Kstop) (Sskip--Kstop) t) sm
                     (AtomState Sskip (st4--Kstop) (Sskip--Kstop) t) tm
  | match_12':
      forall sm tm t,
        gmeminv sm tm->
        t = setid (setid init_tmp r Vzero) x Vone ->
        match_unlock (AtomState Sskip (st4--Kstop) (Sskip--Kstop) t) sm
                     (AtomState Sskip (st4--Kstop) (Sskip--Kstop) t) tm
  | match_13':
      forall sm tm t,
        gmeminv sm tm->
        t = setid (setid init_tmp r Vzero) x Vone ->
        match_unlock (AtomState st4 Kstop (Sskip--Kstop) t) sm
                     (AtomState st4 Kstop (Sskip--Kstop) t) tm
  | match_14':
      forall sm tm t,
        gmeminv sm tm->
        (*(forall sfl sfm, embed sm sfl sfm -> loadmax sfm b = Some Vone) ->*)
        t = setid (setid init_tmp r Vzero) x Vone ->
        match_unlock (AtomState Sskip Kstop (Sskip--Kstop) t) sm
                     (AtomState Sskip Kstop (Sskip--Kstop) t) tm
  | match_15':
      forall sm tm t,
        gmeminv sm tm->
        (*(forall sfl sfm, embed sm sfl sfm -> loadmax sfm b = Some Vone) ->*)
        t = setid (setid init_tmp r Vzero) x Vone ->
        match_unlock (ExtAtomState  (Sskip--Kstop) t) sm
                     (ExtAtomState  (Sskip--Kstop) t) tm
  | match_16':
      forall sm tm t,
        gmeminv sm tm->
        (*(forall sfl sfm, embed sm sfl sfm -> loadmax sfm b = Some Vone) ->*)
        t = setid (setid init_tmp r Vzero) x Vone ->
        match_unlock (State Sskip (Sskip--Kstop) t) sm
                     (State Sskip (Sskip--Kstop) t) tm
  | match_17':
      forall sm tm t,
        gmeminv sm tm->
        (*(forall sfl sfm, embed sm sfl sfm -> loadmax sfm b = Some Vone) ->*)
        t = setid (setid init_tmp r Vzero) x Vone ->
        match_unlock (State Sskip Kstop t) sm
                     (State Sskip Kstop t) tm.
  Lemma match_unlock_match_mem:
    forall m c m' c',
      match_unlock c m c' m'->
      gmeminv m m'.
  Proof. inversion 1;subst;auto. Qed.
  Lemma match_unlock_eq:
    forall m s k te m' s' k' te',
      match_unlock (State s k te) m (State s' k' te') m'->
      s = s' /\ k = k' /\ tmp_inj te te'.
  Proof.
    inversion 1;subst;Esimpl;eauto with tmpls;    eapply setid_inj;eauto with tmpls;try constructor;eapply setid_inj;eauto with tmpls;constructor.
  Qed.
  Lemma match_unlock_eq2:
    forall m s k te m' sc,
      match_unlock (State s k te) m sc m'->
      exists te',sc = State s k te' /\ tmp_inj te te'.
  Proof.
    inversion 1;subst;Esimpl;eauto with tmpls;    eapply setid_inj;eauto with tmpls;try constructor;eapply setid_inj;eauto with tmpls;constructor.
  Qed.
  Lemma match_unlock_eq3:
    forall m s k te m' s' k' te' k2 k2',
      match_unlock (AtomState s k k2 te) m (AtomState s' k' k2' te') m'->
      s = s' /\ k = k' /\ k2 = k2' /\ tmp_inj te te'.
  Proof.
    inversion 1;subst;Esimpl;eauto with tmpls;    eapply setid_inj;eauto with tmpls;try constructor;eapply setid_inj;eauto with tmpls;constructor.
  Qed.
  Lemma match_unlock_eq4:
    forall m s k k2 te m' sc,
      match_unlock (AtomState s k k2 te) m sc m'->
      exists te',sc = AtomState s k k2 te' /\ tmp_inj te te'.
  Proof.
    inversion 1;subst;Esimpl;eauto with tmpls;    eapply setid_inj;eauto with tmpls;try constructor;eapply setid_inj;eauto with tmpls;constructor.
  Qed.
  Lemma match_normal_step_unlock:
  forall sfp  s k te m s' k' te' m' ,
    normalstep sge s k te m sfp s' k' te' m'->
    forall s2 k2 te2 tm,
      match_unlock (State s k te) (strip m) (State s2 k2 te2) (strip tm) ->
      exists tfp tm' ,
        normalstep tge s2 k2 te2 tm tfp s' k' te' tm'/\
        match_unlock (State s' k' te') (strip m') (State s' k' te') (strip tm').
  Proof.
    intros.
    inv H0;inv H.
    all: try(Esimpl;eauto; econstructor;eauto;fail).
  Qed.

  Lemma match_atomic_step_unlock:
    forall sfp  s k te m s' k' te' m' ,
      normalstep sge s k te m sfp s' k' te' m'->
      forall s2 k2 te2 tm k0 k3,
        match_unlock (AtomState s k k0 te) (strip m) (AtomState s2 k2 k3 te2) (strip tm) ->
        exists tfp tm' te2',
          normalstep tge s2 k2 te2 tm tfp s' k' te2' tm'/\
          match_unlock (AtomState s' k' k0 te') (strip m') (AtomState s' k' k3 te2') (strip tm').
  Proof.
    intros.
    inv H0;inv H.
    all: try(Esimpl;eauto; econstructor;eauto;fail).
    {
      rewrite SFIND in H2;inversion H2;clear H2;subst b0.
      exploit gmeminv_loadmax_inj;eauto;try constructor;auto.
      intros [?[]].
      Esimpl. econstructor. eauto. eauto. eauto. reflexivity.
      Esimpl;eauto;econstructor;eauto.
      exists v. split;try congruence. unfold setid. auto.
      exists x. unfold setid;split;try congruence.
      apply setid_inj;auto with tmpls.
      exploit gmeminv_loadmax_rel;eauto.
    }
    {
      Hsimpl;subst.
      Esimpl;eauto;econstructor;eauto;try reflexivity.
      unfold tmp_check2.
      exists x0. apply functional_extensionality. intro.
      ex_match2;auto. rewrite setid_comm. subst x1. rewrite setid_i;auto.
      intro R;inv R.
      unfold setid. ex_match2.
      unfold tmp_check2.
      exists x. apply functional_extensionality. intro.
      ex_match2;auto. rewrite setid_comm. subst x1. rewrite setid_i;auto.
      intro R;inv R.
      unfold setid. ex_match2.

      apply setid_inj;auto with tmpls.
    }
    {
      inv H1. unfold tmp_check2 in *.
      Hsimpl.
      specialize (H14 r). rewrite H0 in H14.
      inv H14. rewrite setid_i in H0. subst x0.
      rewrite setid_i in H4. subst x.
      Esimpl;eauto;econstructor;eauto;try constructor.
      rewrite setid_i;auto.
      rewrite setid_comm;auto.
      intro;discriminate.
    }
    {
      rewrite setid_i in H4.
      assert(exists m,storemax tm b' Vone = Some m).
      pose proof mu_inj_b.
      destruct H11;Hsimpl.
      eapply grange_perm_eq2 in H3 as ?;eauto.
      2: unfold Bset.inj_to_meminj;rewrite H;eauto.
      unfold storemax. ex_match2;eauto.
      clear Hx;contradict n;eauto.
      solv_eq; unfold storemax in H4; ex_match;auto.
      Hsimpl.
      Esimpl;eauto;econstructor;eauto.
      rewrite SFIND in H2. inversion H2;clear H2;subst b0.
      eapply store_gmeminv;eauto. 
    }
  Qed.
  
  Definition match_core (flag:bool) sc sm tc tm:=
  if flag then match_lock sc sm tc tm else match_unlock sc sm tc tm.
 End MATCHSTATE. 
(*
Inductive match_state_fmem:bool->Mu->meminj->core->mem->core->mem->Prop:=
| mk_match_state_fmem:
    forall sc tc sm tm j' flag mu 
      (GEINIT:ge_init_inj mu sge tge)
      (INJINCR:inject_incr j j')
      (MEMINJ: Finject j' sm tm)
      (SMEMINV: Meminv sm)
      (TMEMINV: Meminv2 tm)
      (COREEQ: match_core flag sc (strip sm) tc (strip tm))      
      (SRC:MemClosures.reach_closed (strip sm) (SharedSrc mu))
      (TRC:MemClosures.reach_closed (strip tm) (SharedTgt mu))
      (SVALID:forall b, Bset.belongsto (Injections.SharedSrc mu) b -> Mem.valid_block sm b)
      (TVALID:forall b, Bset.belongsto (Injections.SharedTgt mu) b -> Mem.valid_block tm b)
      (AGMU:proper_mu sge tge j' mu)
      (SLAP: no_overlap (Mem.freelist sm) (SharedSrc mu))
      (SREP: norep (Mem.freelist sm))
      (TLAP: no_overlap (Mem.freelist tm) (SharedTgt mu))
      (TREP: norep (Mem.freelist tm)),
      match_state_fmem flag  mu j' sc sm tc tm.
*)
Inductive match_state:freelist->freelist->bool->Mu->meminj->core*gmem->core*gmem->Prop :=
| mk_match_state:
    forall sc tc sm tm j' flag tfl sfl mu 
      (GEINIT:ge_init_inj mu sge tge)
      (INJINCR:inject_incr j j')
      (TEMBED:exists tfm, embed tm tfl tfm)
      (*MEMREL:forall sfm, embed sm sfl sfm ->  exists tfm, embed tm tfl tfm*)
      (*SMEMINV: forall sfm, embed sm sfl sfm->Meminv sfm*)
      (*TMEMINV:forall tfm, embed tm tfl tfm->Meminv2 tfm*)
      (FLINJ: forall b b' ofs, in_fl sfl b-> j' b = Some (b',ofs)->in_fl tfl b')
      (COREINJ: match_core mu flag sc sm tc tm)
      (AGMU:proper_mu sge tge j' mu)
      (*SVALID:forall b, Bset.belongsto (Injections.SharedSrc mu) b -> GMem.valid_block sm b)
      (TVALID:forall b, Bset.belongsto (Injections.SharedTgt mu) b -> GMem.valid_block tm b*)
      (SLAP: no_overlap sfl (SharedSrc mu))
      (SREP: norep sfl)
      (TLAP: no_overlap tfl (SharedTgt mu))
      (TREP: norep tfl),
      match_state sfl tfl flag mu j' (sc,sm) (tc,tm).
(*
Lemma match_state_with_fmem:
  forall mu flag f sfl tfl sc tc sm tm sfm ,
    match_state sfl tfl flag mu f (sc,sm)(tc,tm)->
    embed sm sfl sfm->
    forall tfm,
      embed tm tfl tfm->
      match_state_fmem flag  mu f sc sfm tc tfm.
Proof.
  intros.
  inv H.
  inversion H0. inversion H1.
  econstructor;eauto.
  rewrite <- H2,<-H4 in MEMINJ.
  inv MEMINJ.
  econstructor;eauto.
  inv ginj0. econstructor;eauto.
  inv mi_inj.
  econstructor;eauto;econstructor;eauto.
  congruence.
  congruence.
  congruence.
  intros.
  rewrite <- H2 in SVALID. unfold GMem.valid_block,strip in SVALID;simpl in SVALID.
  unfold Mem.valid_block. auto.
  intros.
  rewrite <- H4 in TVALID. unfold GMem.valid_block,strip in TVALID;simpl in TVALID.
  unfold Mem.valid_block. auto.
  rewrite H;auto.
  rewrite H;auto.
  rewrite H3;auto.
  rewrite H3;auto.
Qed.
Lemma match_state_fmem_down:
  forall mu flag f sc sfm tc tfm,
    match_state_fmem flag mu f sc sfm tc tfm ->
    match_state (Mem.freelist sfm)(Mem.freelist tfm) flag mu f (sc,(strip sfm))(tc,(strip tfm)).
Proof.
  intros.
  inv H.
  econstructor;eauto.
  intros. exists tfm.
  constructor;auto.
  inv MEMINJ. econstructor;eauto.
  inv inj0. econstructor;eauto.
  inv mi_inj. econstructor;eauto.
  {
    intros.
    revert H SMEMINV;clear.
    destruct sfm,sfm0;simpl.
    intros.
    inv H. unfold strip in *. simpl in *.
    inv H1.
    unfold Meminv,loadmax in *.
    simpl in *. auto.
  }
  {
    revert TMEMINV.
    clear. intros.
    destruct tfm,tfm0;simpl in *.
    inv H.
    unfold strip,Meminv,loadmax in *;simpl in *.
    inv H1. auto.
  }
  inv MEMINJ. inv inj0. auto.
Qed.
*)
Definition MS sfl tfl mu fp fp' cm cm' :Prop:=
  exists b, match_state sfl tfl b mu (Bset.inj_to_meminj (Injections.inj mu)) cm cm' /\ LfpG' tfl mu fp fp'.

Lemma LfpG_emp:
  forall mu fl fp, LfpG' mu fl fp FP.emp.
  constructor;constructor;try constructor;intros;try inv H;try inv H0.
Qed.
Lemma Inv_Ginj:
  forall mu m m',
    Inv mu m m'->
    Ginject (Bset.inj_to_meminj (Injections.inj mu)) m m'.
Proof.
  unfold Inv.
  intros.
  econstructor;eauto.
  inv H. inv mi_inj.
  eauto.
Qed.
Lemma embed_preserve:
  forall fl m fm,
    embed m fl fm->
    forall m',
      GMem.forward m m'->
      unchg_freelist fl m m'->
      exists fm', embed m' fl fm'.
Proof.
  intros.
  inv H.
  inv H1.
  pose proof gmem_fl_wd_embed.
  pose proof fmem_strip_fl_wd fm.
  assert(gmem_fl_wd m' (Mem.freelist fm)(Mem.nextblockid fm)).
  inv H1.
  constructor;auto.
  intros.
  apply valid_wd0 in H1 as ?.
  unfold get_block in H1. unfold in_fl in unchanged_on_validity.
  assert(exists n, Streams.Str_nth n (Mem.freelist fm) = b0).
  eauto.
  specialize (unchanged_on_validity _ 0 H3) as ?.
  clear H1 H3.
  unfold GMem.valid_block in H4.
  split;intro;eauto. apply H4 in H1. apply H2. auto.
  apply H2 in H1. apply H4. auto.

  eexists. eapply H with(wd:=H2);eauto.
Qed.
Lemma fmem_valid_wd:
  forall (m:mem) n b,
    get_block m.(Mem.freelist) n = b ->
    In b m.(Mem.validblocks) <-> (n<m.(Mem.nextblockid))%coq_nat.
Proof.
  destruct m;simpl;intros;auto.
Qed.
Lemma init_embed:
  forall mu sfl tfl sm tm,
    ge_init_inj mu sge tge->
    init_gmem tge tm->
    local_init_rel mu sfl sm tfl tm->
    exists fm, embed tm tfl fm.
Proof.
  unfold init_gmem; intros.
  Hsimpl.
  inv H2.
  unfold Mem.valid_block in dom_match_fm.
  pose proof fmem_valid_wd x as x_valid_wd.
  enough(gmem_fl_wd (strip x) tfl 0).
  Hsimpl.
  eexists; eapply gmem_fl_wd_embed with(wd:=H0) ;eauto.

  inv H1.
  unfold valid_block_bset,GMem.valid_block,strip in tfl_free;simpl in tfl_free.
  econstructor;eauto.
  inv tfl_norep;auto.
  unfold strip;simpl.
  intros.
  
  apply tfl_free in H0.
  unfold Bset.belongsto in H0.
  split;intro;try contradiction;try Lia.lia.
Qed.
Lemma gmeminv_HLRELY:
  forall mu sfl tfl Hm Lm Hm' Lm',
    gmeminv mu Hm Lm ->
    HLRely sfl tfl mu Hm Hm' Lm Lm'->
    ge_init_inj mu sge tge->
    gmeminv mu Hm' Lm'.
Proof.
  unfold gmeminv;intros;Hsimpl.
  inv H0. inv H5;inv H4.
  Esimpl;eauto.
  apply Inv_Ginj;auto.
Qed.


Lemma initsim:
  forall mu argSrc argTgt sc id
    (ARGREL: arg_rel (Injections.inj mu) argSrc argTgt)
    (INITCORE: init_core sge id argSrc = Some sc)
    (GEINIT:ge_init_inj mu sge tge),
  init_core tge id argTgt = Some sc /\
  forall sm tm sfl tfl,
    init_gmem sge sm->
    init_gmem tge tm->
    local_init_rel mu sfl sm tfl tm->
    forall sm' tm',
      HLRely sfl tfl mu sm sm' tm tm'->
      MS sfl tfl mu FP.emp FP.emp (sc,sm')(sc,tm').
Proof.
  intros.
  exploit lock_init_state.
  eexact SGEINIT. eauto.
  intro.
  Hsimpl. subst.
  inv ARGREL.
  assert(init_core tge id nil = Some sc).
  destruct H0;subst.
  exploit lock_release_init_state.
  eexact SGEINIT.
  intros.
  rewrite INITCORE in H.
  assert(sc = (CallStateIn (fn_body lock_release_fnbody))).
  inv H;auto.
  rewrite H0 in *;clear H H0 sc.
  exploit lock_release_init_state.
  eexact TGEINIT.
  intros. auto.

  exploit lock_acquire_init_state.
  eexact SGEINIT.
  intros.
  rewrite INITCORE in H.
  assert(sc = (CallStateIn (fn_body lock_acquire_fnbody))).
  inv H;auto.
  rewrite H0 in *;clear H H0 sc.
  exploit lock_acquire_init_state.
  eexact TGEINIT.
  intros. auto.

  pose proof GEINIT as GEINIT'.
  split;auto. intros.
  exists (if peq id lock_release_ident then false else true).
  split;try apply LfpG_emp.
  pose proof H3 as LOCALINIT.
  inv H3;inv H4;Hsimpl;inv GEINIT.
  econstructor;eauto.
  {
    unfold inject_incr.
    intros.
    unfold j in H9.
    ex_match;subst.
    specialize (senv_injected lock_L_ident).
    unfold Senv.find_symbol,Genv.to_senv,F,V in senv_injected.
    rewrite SFIND,TFIND in senv_injected.
    inv senv_injected. inv H9. unfold Bset.inj_to_meminj;rewrite H13;auto.
    specialize (senv_injected lock_acquire_ident).
    unfold Senv.find_symbol,Genv.to_senv,F,V in senv_injected.
    rewrite SFIND2,TFIND2 in senv_injected.
    inv senv_injected. inv H9. unfold Bset.inj_to_meminj;rewrite H13;auto.
    specialize (senv_injected lock_release_ident).
    unfold Senv.find_symbol,Genv.to_senv,F,V in senv_injected.
    rewrite SFIND3,TFIND3 in senv_injected.
    inv senv_injected. inv H9. unfold Bset.inj_to_meminj;rewrite H13;auto.
  }
  {
    eapply init_embed in LOCALINIT;eauto.
    Hsimpl.
    inv H5;eapply embed_preserve;eauto.
  }
  {
    intros.
    unfold Bset.inj_to_meminj in H10.
    ex_match.
    inv H10.
    apply mu_inject in Hx.
    apply valid_Src in Hx.
    destruct H9.
    apply sfl_free in H9.
    contradiction.
  }
  destruct peq;subst.
  {
    exploit lock_release_init_state;try eexact SGEINIT;intro.
    rewrite INITCORE in H9. inv H9.
    simpl.
    econstructor;eauto.
    unfold gmeminv.
    inv H3. inv H5.
    Esimpl;eauto.
    eapply Inv_Ginj;eauto.
  }
  {
    destruct H0;try congruence;subst.
    exploit lock_acquire_init_state;try eexact SGEINIT;intro.
    rewrite INITCORE in H0;inv H0;econstructor;eauto.
    unfold gmeminv.
    inv H3. inv H5.
    Esimpl;eauto.
    eapply Inv_Ginj;eauto.
  }
  inv H3. inv H9. auto.
  inv H5. inv H9. auto.
  {
    constructor;auto.
    unfold sep_inject.
    auto.
  }
Qed.

Lemma match_external:
  forall (mu : Mu) (Hfp Lfp : footprint)
    (Hcore : core ) 
    (Hm : gmem) (Lcore : core)
    (Lm : gmem) (f : ident) (sg : signature)
    (argSrc : list val) sfl tfl,
    MS sfl tfl mu Hfp Lfp (Hcore, Hm) (Lcore, Lm) ->
    at_external sge Hcore = Some (f, sg, argSrc) ->
    HG sfl mu Hfp Hm ->
    G_args (SharedSrc mu) argSrc ->
    exists (argTgt : list val),
      at_external tge Lcore = Some (f, sg, argTgt) /\
      arg_rel (Injections.inj mu) argSrc argTgt /\
      LG' tfl mu Hfp Hm Lfp Lm /\
      MS sfl tfl mu FP.emp FP.emp (Hcore, Hm) (Lcore, Lm).
Proof.
  intros.
  unfold MS in*. Hsimpl.
  unfold at_external in *.
  ex_match;subst.
  inv H. inv H0.
  destruct x.
  inv COREINJ.
  Esimpl;eauto. constructor.
  {
    inv H3.
    destruct H5 as (?&?&?);auto.
    inv H5.
    constructor;auto.
    constructor;auto.
  }
  instantiate(1:=true).
  econstructor;eauto.
  econstructor;eauto.
  apply LfpG_emp.

  simpl in COREINJ.
  inv COREINJ.
  Esimpl;eauto. constructor.
  {
    inv H3.
    destruct H8 as (?&?&?);auto.
    inv H5.
    constructor;auto.
    constructor;auto.
  }
  instantiate(1:=false).
  econstructor;eauto.
  econstructor;eauto.
  apply LfpG_emp.

  inv H. inv H0.
  destruct x.
  inv COREINJ.
  Esimpl;eauto. constructor.
  {
    inv H3.
    destruct H4 as [?[?[]]].
    constructor;auto.
    constructor;auto.
  }
  instantiate(1:=true).
  econstructor;eauto.
  econstructor;eauto.
  apply LfpG_emp.

  inv COREINJ.
  Esimpl;eauto. constructor.
  {
    inv H3. destruct H4 as [?[?[]]].
    constructor;auto.
    constructor;auto.
  }
  instantiate(1:=false).
  econstructor;eauto.
  econstructor;eauto.
  apply LfpG_emp.
Qed.

Lemma match_afterext:
 forall (mu : Mu)
   (Hcore : core) 
   (Hm : gmem) (Lcore : core)
   (Lm : gmem) (oresSrc : option val)
   (Hcore' : core)
   (oresTgt : option val) sfl tfl,
   MS sfl tfl mu FP.emp FP.emp (Hcore, Hm) (Lcore, Lm) ->
   G_oarg (SharedSrc mu) oresSrc ->
   after_external Hcore oresSrc =
   Some Hcore' ->
   ores_rel (Injections.inj mu) oresSrc oresTgt ->
   exists Lcore',
     after_external Lcore oresTgt =
     Some Lcore' /\
     (forall Hm' Lm' : GMem.gmem',
         HLRely sfl tfl mu Hm Hm' Lm Lm' ->
         MS sfl tfl mu FP.emp FP.emp (Hcore', Hm') (Lcore', Lm')).
Proof.
  unfold after_external;intros;ex_match;subst.
  inv H1. unfold ores_rel in H2. destruct oresTgt;try contradiction;clear H2.
  unfold MS in *. Hsimpl.
  inv H. 
  destruct x.
  {
    inv COREINJ.
    Esimpl;eauto.
    intros.
    exists true.
    Esimpl;try apply LfpG_emp.
    {
      econstructor;eauto.
      {
        Hsimpl.
        inv H. inv H6.
        eapply embed_preserve;eauto.
      }
      econstructor;eauto.
      eapply gmeminv_HLRELY;eauto.
    }
  }
  {
    inv COREINJ.
    Esimpl;eauto.
    intros.
    exists false.
    Esimpl;try apply LfpG_emp.
    {
      econstructor;eauto.
      {
        Hsimpl.
        inv H. inv H4.
        eapply embed_preserve;eauto.
      }
      econstructor;eauto.
      eapply gmeminv_HLRELY;eauto.
    }
  }
  
  inv H1. unfold ores_rel in H2. destruct oresTgt;try contradiction;clear H2.
  unfold MS in *.
  Hsimpl. inv H.
  destruct x.
  {
    inv COREINJ.
    Esimpl;eauto.
    intros.
    exists true.
    Esimpl;try apply LfpG_emp.
    
    econstructor;eauto.
    {
      Hsimpl.
      inv H. inv H7.
      eapply embed_preserve;eauto.
    }
    econstructor;eauto.
    eapply gmeminv_HLRELY;eauto.
  }
  {
    inv COREINJ.
    Esimpl;eauto.
    intros.
    exists false.
    Esimpl;try apply LfpG_emp.
    
    econstructor;eauto.
    {
      Hsimpl.
      inv H. inv H5.
      eapply embed_preserve;eauto.
    }
    econstructor;eauto.
    eapply gmeminv_HLRELY;eauto.
  }
Qed.
Lemma match_halt:
   forall  (mu : Mu) (Hfp Lfp : footprint)
      (Hcore : core) 
      (Hm : gmem) (Lcore :core) 
      (Lm : gmem) (resSrc : val) sfl tfl,
     MS sfl tfl mu Hfp Lfp (Hcore, Hm) (Lcore, Lm) ->
     halt Hcore = Some resSrc ->
     HG sfl mu Hfp Hm ->
     G_arg (SharedSrc mu) resSrc ->
     exists resTgt : val,
       halt Lcore = Some resTgt /\
       res_rel (Injections.inj mu) resSrc resTgt /\
       LG' tfl mu Hfp Hm Lfp Lm.
Proof.
  unfold halt,MS;intros;Hsimpl.
  ex_match. inv H0.
  inv H.
  destruct x;inv COREINJ;Esimpl;eauto;  constructor;  inv H3;auto.
  1,3:constructor;auto.
  all: destruct H0 as [?[?[]]];auto.
Qed.

Lemma range_perm_eq:
  forall f m b m2 b',
    Finject f m m2->
    f b = Some (b',0)->
    Mem.range_perm m b 0 4 Max Writable->
    Mem.range_perm m2 b' 0 4 Max Writable.
Proof.
  unfold Mem.range_perm;intros.
  inv H. inv inj0. inv mi_inj.
  eapply mi_perm in H0;eauto.
  assert(ofs + 0 = ofs). Lia.lia.
  congruence.
Qed.
Lemma fstep_fleq:
  forall ge c m fp c' m',
    fstep ge c m fp c' m'->
    Mem.freelist m = Mem.freelist m'.
Proof.
  inversion 1;subst.
  inv H0;subst;auto.
  unfold storemax in H3. ex_match2. inv H3. auto.
  inv H;auto. inv H0;auto. unfold storemax in H3;ex_match2;inv H3;auto.
  inv H;auto.
  apply mem_alloc_fleq in H0;auto.
Qed.

Lemma LfpG_loadb:
  forall mu fl,
    ge_init_inj mu sge tge->
    no_overlap fl (SharedTgt mu) ->
    LfpG' fl mu (loadmax_fp b)(loadmax_fp b').
Proof.
  intros. unfold loadmax_fp,FMemOpFP.load_fp,FMemOpFP.range_locset,Locs.belongsto.
  inv H. unfold Senv.find_symbol,Genv.to_senv,F,V in senv_injected.
  specialize (senv_injected lock_L_ident).
  rewrite SFIND,TFIND in senv_injected. inv senv_injected.
  constructor.
  constructor;try apply FMemOpFP.emp_loc_match.
  unfold FP.ge_reads;simpl;constructor;unfold Locs.belongsto;intros.
  ex_match. subst b0.
  Esimpl. eauto.
  unfold Locs.union. apply orb_true_iff. left.
  ex_match2.

  constructor. unfold Bset.belongsto,FP.blocks,FP.locs,Locs.blocks,Locs.belongsto in H. simpl in H.
  rewrite ! Locs.emp_union_locs in H.
  rewrite Locs.locs_union_emp in H.
  Hsimpl.
  ex_match. subst b0.
  inv mu_inject.
  inv inj_weak.
  eapply inj_range';eauto.
Qed.
Lemma LfpG_storeb:
  forall mu fl,
    ge_init_inj mu sge tge->
    no_overlap fl (SharedTgt mu) ->
    LfpG' fl mu (storemax_fp b)(storemax_fp b').
Proof.
  intros. unfold storemax_fp,FMemOpFP.store_fp,FMemOpFP.range_locset,Locs.belongsto.
  inv H. unfold Senv.find_symbol,Genv.to_senv,F,V in senv_injected.
  specialize (senv_injected lock_L_ident).
  rewrite SFIND,TFIND in senv_injected. inv senv_injected.
  constructor.
  constructor;try apply FMemOpFP.emp_loc_match.
  unfold FP.ge_writes;simpl;constructor;unfold Locs.belongsto;intros.
  ex_match. subst b0.
  Esimpl. eauto.
  unfold Locs.union. apply orb_true_iff. left.
  ex_match2.

  constructor. unfold Bset.belongsto,FP.blocks,FP.locs,Locs.blocks,Locs.belongsto in H. simpl in H.
  rewrite ! Locs.emp_union_locs in H.
  rewrite Locs.locs_union_emp in H.
  Hsimpl.
  ex_match. subst b0.
  inv mu_inject.
  inv inj_weak.
  eapply inj_range';eauto.
Qed.
Transparent Mem.alloc.
Lemma alloc_reach'':
  forall l m m' stk,
    no_overlap (Mem.freelist m) l->
    Mem.alloc m 0 0 = (m',stk) ->
    (forall L b, MemClosures.reach' (strip m) l L b -> Bset.belongsto l b) ->
    forall L b,
      MemClosures.reach' (strip m') l L b->
      MemClosures.reach' (strip m) l L b.
Proof.
  induction L;intros.
  inv H2;auto. constructor;auto.
  inv H2.
  specialize (IHL _ H5).
  specialize (H1 _ _ IHL).
  assert(b'0<>stk).
  apply Mem.alloc_result in H0.
  symmetry in H0. apply H in H0 as ?.
  intro;subst;congruence.

  exploit Mem.perm_alloc_4;eauto;intro.
  econstructor;eauto.
  instantiate(1:=n). instantiate(1:=q).
  rewrite <- H8.
  unfold strip;simpl.
  unfold Mem.alloc in H0. inv H0;simpl.
  rewrite PMap.gsspec.
  ex_match2;auto.
Qed.

Lemma alloc_rc:
  forall l m m' stk,
    no_overlap (Mem.freelist m) l->
    Mem.alloc m 0 0 = (m',stk)->
    MemClosures.reach_closed (strip m) l->
    MemClosures.reach_closed (strip m') l.
Proof.
  intros.
  inv H1.
  constructor.
  {
    clear no_undef no_vundef.

    intros.
    inv H1. 
    eapply alloc_reach'' in H2;eauto.
    apply reachable_closure;eauto. econstructor;eauto.
    intros.
    apply reachable_closure. econstructor;eauto.
  }
  1,2: unfold Mem.alloc,GMem.perm in *;inv H0;simpl in *.
  {
    clear reachable_closure no_vundef.
    intros.
    rewrite PMap.gsspec in H1.
    destruct peq.
    unfold Mem.nextblock,get_block in e.
    unfold no_overlap in H.
    symmetry in e.
    apply H in e. contradiction.

    apply no_undef in H1;auto.
    rewrite PMap.gso;auto. 
  }
  {
    clear reachable_closure no_undef.
    intros.
    rewrite PMap.gsspec in H1.
    destruct peq.
    unfold Mem.nextblock,get_block in e.
    unfold no_overlap in H.
    symmetry in e.
    apply H in e. contradiction.

    rewrite PMap.gso;auto. 
  }
Qed.
Lemma alloc_mem_inj_1:
  forall mu m1 m2,
    GMem.mem_inj (Bset.inj_to_meminj(Injections.inj mu)) (strip m1)(strip m2)->
    Bset.inject (Injections.inj mu)(SharedSrc mu) (SharedTgt mu)->
    no_overlap (Mem.freelist m1)(SharedSrc mu)->
    forall m3 z,
      Mem.alloc m1 0 0 = (m3, z)->
      GMem.mem_inj (Bset.inj_to_meminj(Injections.inj mu)) (strip m3)(strip m2).
Proof.
  intros.
  inv H.
  assert(mi_perm' : forall (b1 b2 : block) (delta ofs : Z) (k : perm_kind) (p : permission),
            Bset.inj_to_meminj (Injections.inj mu) b1 = Some (b2, delta) ->
            GMem.perm (strip m3) b1 ofs k p -> GMem.perm (strip m2)b2 (ofs + delta) k p).
  intros.
  eapply mi_perm in H;eauto.
  exploit Mem.perm_alloc_4;eauto.
  intro. subst.
  apply Mem.alloc_result in H2.
  symmetry in H2. apply H1 in H2.
  unfold Bset.inj_to_meminj in H.
  ex_match.
  inv H0. inv inj_weak.
  apply inj_dom' in Hx.
  contradiction.
  constructor;auto.
  {
    intros.
    eapply mi_align in H;eauto.
    instantiate(1:=p). instantiate(1:=ofs).
    unfold GMem.range_perm in *;intros.
    apply H3 in H4;eauto.
    exploit Mem.perm_alloc_4;eauto.
    intro. subst.
    apply Mem.alloc_result in H2.
    symmetry in H2. apply H1 in H2.
    unfold Bset.inj_to_meminj in H.
    ex_match.
    inv H0. inv inj_weak.
    apply inj_dom' in Hx.
    contradiction.
  }
  {
    intros.
    assert(b1 <> Mem.nextblock m1).
    intro. symmetry in H4.
    apply H1 in H4.
    unfold Bset.inj_to_meminj in H.
    ex_match.
    inv H0. inv inj_weak.
    apply inj_dom' in Hx.
    contradiction.
    eapply mi_memval in H;eauto.
    revert H.
    instantiate(1:=ofs).
    intro.
    unfold Mem.alloc in H2;inv H2;simpl in *.
    rewrite PMap.gso;auto.

    exploit Mem.perm_alloc_4;eauto.
    apply Mem.alloc_result in H2;auto. congruence.
  }
Qed.
Lemma alloc_mem_inj_2:
  forall mu m1 m2,
    GMem.mem_inj (Bset.inj_to_meminj(Injections.inj mu)) (strip m1)(strip m2)->
    Bset.inject (Injections.inj mu)(SharedSrc mu) (SharedTgt mu)->
    no_overlap (Mem.freelist m2)(SharedTgt mu)->
    forall m3 z,
      Mem.alloc m2 0 0 = (m3, z)->
      GMem.mem_inj (Bset.inj_to_meminj(Injections.inj mu)) (strip m1)(strip m3).
Proof.
  intros.
  inv H.
  assert(mi_perm' : forall (b1 b2 : block) (delta ofs : Z) (k : perm_kind) (p : permission),
            Bset.inj_to_meminj (Injections.inj mu) b1 = Some (b2, delta) ->
            GMem.perm (strip m1) b1 ofs k p -> GMem.perm (strip m3)b2 (ofs + delta) k p).
  intros.
  eapply mi_perm in H;eauto.
  exploit Mem.perm_alloc_1;eauto.
  constructor;auto.
  {
    intros.
    assert(b0 <> Mem.nextblock m2).
    intro. symmetry in H4.
    apply H1 in H4.
    unfold Bset.inj_to_meminj in H.
    ex_match.
    inv H0. inv inj_weak.
    apply inj_range' in Hx. inv H.
    contradiction.
    eapply mi_memval in H;eauto.
    unfold Mem.alloc in H2;inv H2;simpl in *.
    rewrite PMap.gso;auto.
  }
Qed.

Lemma alloc_mem_inj:
  forall mu m1 m2,
    GMem.mem_inj (Bset.inj_to_meminj(Injections.inj mu)) (strip m1)(strip m2)->
    Bset.inject (Injections.inj mu)(SharedSrc mu) (SharedTgt mu)->
    no_overlap (Mem.freelist m1)(SharedSrc mu)->
    no_overlap (Mem.freelist m2)(SharedTgt mu)->
    forall m3 m4 z2 z,
      Mem.alloc m1 0 0 = (m3, z)->
      Mem.alloc m2 0 0 = (m4, z2)->
      GMem.mem_inj (Bset.inj_to_meminj(Injections.inj mu)) (strip m3)(strip m4).
Proof.
  intros.
  exploit alloc_mem_inj_1;eauto.
  intros.
  exploit alloc_mem_inj_2;eauto.
Qed.
Lemma alloc_inj:
  forall mu m1 m2,
    Ginject (Bset.inj_to_meminj(Injections.inj mu))(strip m1)(strip m2)->
    Bset.inject (Injections.inj mu)(SharedSrc mu) (SharedTgt mu)->
    no_overlap (Mem.freelist m1)(SharedSrc mu)->
    no_overlap (Mem.freelist m2)(SharedTgt mu)->
    forall m3 m4 z z2,
      Mem.alloc m1 0 0 = (m3, z)->
      Mem.alloc m2 0 0 = (m4, z2)->
      Ginject (Bset.inj_to_meminj(Injections.inj mu))(strip m3)(strip m4).
Proof.
  intros.
  inv H. inv ginj0.
  eapply alloc_mem_inj in mi_inj as R;eauto.
  constructor;auto.
  constructor;auto.
  {
    intros.
    apply mi_freeblocks.
    intro;contradict H.
    unfold Mem.alloc in H3;inv H3;unfold strip,GMem.valid_block in H5|- *;simpl in *;auto.
  }
  {
    intros.
    eapply mi_mappedblocks in H;eauto.
    unfold Mem.alloc in H4;inv H4;unfold strip,GMem.valid_block in H|- *;simpl in *;auto.
  }
  {
    unfold GMem.meminj_no_overlap in *;intros.
    assert(b1<>Mem.nextblock m1).
    intro. symmetry in H9. apply H1 in H9.
    unfold Bset.inj_to_meminj in H5;ex_match.
    inv H5. inv H0. inv inj_weak. apply inj_dom' in Hx. contradiction.
    assert(b0<>Mem.nextblock m1).
    intro. symmetry in H10. apply H1 in H10.
    unfold Bset.inj_to_meminj in H6;ex_match.
    inv H6. inv H0. inv inj_weak. apply inj_dom' in Hx. contradiction.
    apply Mem.alloc_result in H3 as ?. subst.
    eapply Mem.perm_alloc_4 in H9;eauto.
    eapply Mem.perm_alloc_4 in H10;eauto.
    exploit mi_no_overlap;eauto.
  }
  {
    intros.
    assert(b0<>Mem.nextblock m1).
    intro. symmetry in H6. apply H1 in H6.
    unfold Bset.inj_to_meminj in H;ex_match.
    inv H. inv H0. inv inj_weak. apply inj_dom' in Hx. contradiction.
    apply Mem.alloc_result in H3 as ?;eauto. subst.
    eapply mi_representable;eauto.
    destruct H5; eapply Mem.perm_alloc_4 in H6;eauto.
    left;auto. right;auto.
  }
  {
    intros.
    assert(b0<>Mem.nextblock m2).
    intro. symmetry in H6. apply H2 in H6.
    unfold Bset.inj_to_meminj in H;ex_match.
    inv H. inv H0. inv inj_weak. apply inj_range' in Hx. contradiction.
    apply Mem.alloc_result in H4 as ?;eauto. subst.
    exploit Mem.perm_alloc_4;eauto.
    intro.
    eapply mi_perm_inv in H7;eauto.
    assert(b1<>Mem.nextblock m1).
    intro. symmetry in H8. apply H1 in H8.
    unfold Bset.inj_to_meminj in H;ex_match.
    inv H. inv H0. inv inj_weak. apply inj_dom' in Hx. contradiction.
    apply Mem.alloc_result in H3 as ?;subst.
    destruct H7.
    eapply Mem.perm_alloc_1 in H3 as ?;eauto.
    right. intro;contradict H7.
    eapply Mem.perm_alloc_4 in H3 as ?;eauto.
  }
  clear mi_freeblocks mi_mappedblocks mi_no_overlap mi_representable mi_perm_inv.
  intros.
  assert(b1<>Mem.nextblock m1).
  intro. symmetry in H6. apply H1 in H6.
  unfold Bset.inj_to_meminj in H;ex_match.
  inv H. inv H0. inv inj_weak. apply inj_dom' in Hx. contradiction.

  pose proof H as R2.
  unfold Bset.inj_to_meminj in R2;ex_match. inv R2.
  apply Mem.alloc_result in H3 as ?;subst.
  apply Mem.alloc_result in H4 as ?;subst.
  eapply Mem.perm_alloc_4 in H5 as ?;eauto.
  assert(Mem.perm m2 b0 ofs Max Readable).
  inv mi_inj. 
  eapply mi_perm in H;eauto.
  assert(ofs+0=ofs). Lia.lia.
  rewrite H8 in H;auto.
  assert(b0<>Mem.nextblock m2).
  intro. symmetry in H9. apply H2 in H9.
  inv H0. inv inj_weak. apply inj_range' in Hx. contradiction.

  eapply gvalinj0 in H as ?;eauto.
  unfold Mem.alloc in *.
  inv H3;inv H4. unfold strip;simpl.
  do 2 (rewrite PMap.gso;auto).
Qed.  
Lemma alloc_zero_gmeminv:
  forall mu m m' stk,
    Bset.inject (Injections.inj mu)(SharedSrc mu) (SharedTgt mu)->
    no_overlap (Mem.freelist m)(SharedSrc mu)->
    Mem.alloc m 0 0 = (m',stk)->
    forall tm,
      gmeminv mu (strip m)(strip tm)->
      no_overlap (Mem.freelist tm)(SharedTgt mu)->
      exists tm' stk',
        Mem.alloc tm 0 0 = (tm',stk')/\ gmeminv mu (strip m')(strip tm').
Proof.
  unfold gmeminv;intros.
  assert(exists tm' stk', Mem.alloc tm 0 0 = (tm',stk')).
  Esimpl;eauto. unfold Mem.alloc;eauto.
  Hsimpl.
  exploit alloc_rc;eauto;intro.
  exploit alloc_rc;try eexact H0;eauto;intro.
  exploit alloc_inj;eauto;intro.
  Esimpl;eauto.
Qed.
Opaque Mem.alloc.
Theorem match_tau_step:
  forall mu sfl tfl Hfp sfp Lfp sm tm c tc c' sm',
    MS sfl tfl mu Hfp Lfp (c, sm) (tc, tm) ->
    step sge sfl c sm sfp c' sm' ->
    HfpG sfl mu sfp ->
  exists tfp tc' tm',
    step tge tfl tc tm tfp tc' tm' /\
    MS sfl tfl mu (FP.union Hfp sfp)(FP.union Lfp tfp) (c',sm')(tc',tm').
Proof.
  intros until sm'.
  unfold MS.
  intros [flag [MATCH LFPG]] STEP HFPG.
  inversion STEP. subst c0 gm fp c'0 gm'.
  inv MATCH. inv H. Hsimpl. inv H.
  pose proof SpecLang_wd  as WD.
  destruct flag.
  {
    inv H0;simpl in *.
    {
      pose proof COREINJ as COREMATCH.
      apply match_lock_eq2 in COREINJ as R.
      destruct R as [te2'[TC TMPINJ]].
      subst tc.
      eapply match_normal_step_lock in COREINJ;eauto.
      Hsimpl.
      Esimpl;eauto.
      econstructor;eauto.
      econstructor;eauto.
      econstructor;eauto.
      econstructor;eauto.
      exists x1. econstructor;eauto. symmetry. eapply fstep_fleq;eauto. econstructor;eauto.
      instantiate(1:=true). auto.
      eapply LfpG'_union;eauto.
      inv COREMATCH;inv H0;inv H;try apply LfpG_emp.
    }
    {
      inv COREINJ.
      Esimpl;eauto.
      econstructor;eauto. econstructor;eauto.
      econstructor 2;eauto.
      econstructor;eauto.
      exists x. econstructor;eauto.
      instantiate(1:=true).
      econstructor;eauto.
      rewrite ! FP.fp_union_emp;auto.
    }
    {
      pose proof COREINJ as COREMATCH.
      apply match_lock_eq4 in COREINJ as R.
      destruct R as [?[? TMPINJ]].
      subst tc.
      eapply match_atomic_step_lock in COREINJ;eauto.
      Hsimpl.
      apply match_lock_match_mem in H1 as ?.
      destruct H2 as (?&?&?).
      Esimpl;eauto.
      econstructor;eauto.
      econstructor;eauto.
      econstructor;eauto.
      instantiate(1:=true). auto.
      econstructor;eauto.
      exists x2. econstructor;eauto. symmetry;eapply fstep_fleq;eauto;econstructor;eauto.
      eapply LfpG'_union;eauto.
      {
        inv COREMATCH;inv H0;inv H;try apply LfpG_emp;
          rewrite SFIND in H6;inversion H6;subst b1;
            rewrite TFIND in H7;inversion H7;subst b0.
        apply LfpG_loadb;auto.
        apply LfpG_storeb;auto.
      }
    }
    {
      inv COREINJ.
      Esimpl;eauto.
      econstructor;eauto. econstructor;eauto.
      econstructor 4;eauto.
      econstructor;eauto.
      eexists;econstructor;eauto.
      instantiate(1:=true).
      econstructor;eauto.
      rewrite ! FP.fp_union_emp;auto.
    }
    inv COREINJ.
    exploit alloc_zero_gmeminv;eauto.
    inv AGMU;auto.
    intro. Hsimpl.
    Esimpl;eauto.
    
    econstructor;eauto. econstructor;eauto. econstructor 5;eauto.
    instantiate(1:=true).
    econstructor;eauto.
    exists x0. econstructor;eauto.
    apply mem_alloc_fleq in H0;auto.
    econstructor;eauto.
    apply LfpG'_union;auto.
    {
      constructor;auto.
      {
        unfold FMemOpFP.alloc_fp,FMemOpFP.uncheck_alloc_fp;simpl.
        constructor;try apply FMemOpFP.emp_loc_match;simpl.
        constructor. unfold Bset.inject_block,Bset.belongsto,Locs.belongsto.
        intros.
        ex_match2.
        clear Hx.
        apply TLAP in e.
        contradiction.
      }
      {
        right.
        unfold FP.blocks,FP.locs,Locs.blocks,FMemOpFP.alloc_fp,FMemOpFP.uncheck_alloc_fp in H3. simpl in H3.
        rewrite ! Locs.emp_union_locs in H3.
        unfold Bset.belongsto,Locs.belongsto in H3.
        Hsimpl. ex_match2.
        unfold Mem.nextblock,get_block in e.
        eauto.
      }
    }
  }
  {
    inv H0;simpl in *.
    {
      pose proof COREINJ as COREMATCH.
      apply match_unlock_eq2 in COREINJ as R.
      destruct R as (?&?&?);subst tc.
      eapply match_normal_step_unlock in COREINJ;eauto.
      Hsimpl.
      apply match_unlock_match_mem in H2 as ?.
      destruct H3 as (?&?&?).
      Esimpl;eauto.
      econstructor;eauto.
      econstructor;eauto.
      econstructor;eauto.
      instantiate(1:=false). auto.

      
      econstructor;eauto.
      exists x2. econstructor;eauto. symmetry;eapply fstep_fleq;eauto;econstructor;eauto.
      eapply LfpG'_union;eauto.
      inv COREMATCH;inv H0;inv H;auto;try apply LfpG_emp.
    }
    {
      inv COREINJ.
      Esimpl;eauto.
      econstructor;eauto. econstructor;eauto.
      econstructor 2;eauto.
      econstructor;eauto.
      eexists;econstructor;eauto.
      instantiate(1:=false).
      econstructor;eauto.
      rewrite ! FP.fp_union_emp;auto.
    }
    {
      pose proof COREINJ as COREMATCH.
      apply match_unlock_eq4 in COREINJ as R.
      destruct R as (?&?&R).
      subst tc.
      eapply match_atomic_step_unlock in COREINJ;eauto.
      Hsimpl.
      apply match_unlock_match_mem in H1 as R2.
      destruct R2 as (R2&R3&R4).
      Esimpl;eauto.
      econstructor;eauto.
      econstructor;eauto.
      econstructor;eauto.
      econstructor;eauto.
      exists x2. econstructor;eauto. symmetry;eapply fstep_fleq;eauto; econstructor ;eauto.
      instantiate(1:=false). auto.
      eapply LfpG'_union;eauto.
      {
        inv COREMATCH;inv H0;inv H;try apply LfpG_emp;
          rewrite SFIND in H3;inversion H3;subst b1;
            rewrite TFIND in H4;inversion H4;subst b0.
        apply LfpG_loadb;auto.
        apply LfpG_storeb;auto.
      }
    }
    {
      inv COREINJ.
      Esimpl;eauto.
      econstructor;eauto. econstructor;eauto.
      econstructor 4;eauto.
      econstructor;eauto.
      eexists;econstructor;eauto.
      instantiate(1:=false).
      econstructor;eauto.
      rewrite ! FP.fp_union_emp;auto.
    }
    {
      inv COREINJ.
      exploit alloc_zero_gmeminv;eauto.
      inv AGMU;auto.
      intro. Hsimpl.
      Esimpl;eauto.
      
      econstructor;eauto. econstructor;eauto. econstructor 5;eauto.
      instantiate(1:=false).
      econstructor;eauto.
      exists x0. econstructor;eauto.
      apply mem_alloc_fleq in H0;auto.
      econstructor;eauto.
      apply LfpG'_union;auto.
      {
        constructor;auto.
        {
          unfold FMemOpFP.alloc_fp,FMemOpFP.uncheck_alloc_fp;simpl.
          constructor;try apply FMemOpFP.emp_loc_match;simpl.
          constructor. unfold Bset.inject_block,Bset.belongsto,Locs.belongsto.
          intros.
          ex_match2.
          clear Hx.
          apply TLAP in e.
          contradiction.
        }
        {
          right.
          unfold FP.blocks,FP.locs,Locs.blocks,FMemOpFP.alloc_fp,FMemOpFP.uncheck_alloc_fp in H3. simpl in H3.
          rewrite ! Locs.emp_union_locs in H3.
          unfold Bset.belongsto,Locs.belongsto in H3.
          Hsimpl. ex_match2.
          unfold Mem.nextblock,get_block in e.
          eauto.
        }
      }
    }
  }
Qed.
End SIMULATION.

Theorem locksim:
  @ldsim speclang speclang lock_comp_unit lock_comp_unit.
Proof.
  unfold ldsim,lock_comp_unit;simpl.
  unfold F,V. intros.
  inv H;simpl in *.
  inv H0;simpl in *.
  set (ge':= (Genv.globalenv
            {|
            prog_defs := (lock_L_ident, lock_L)
                         :: (lock_acquire_ident, lock_acquire)
                            :: (lock_release_ident, lock_release) :: nil;
            prog_public := lock_L_ident
                           :: lock_acquire_ident :: lock_release_ident :: nil;
            prog_main := 1%positive |})) in *.
  assert(ge = ge').
  unfold ge,ge'. auto.
  subst ge'.
  rewrite <- H in *;clear H.
  apply find_lock_gvar_from_ge in H2 as ?.
  destruct H as [sb[SSYMB SVAR]].
  apply find_lock_gvar_from_ge in H3 as ?.
  destruct H as [tb[TSYMB TVAR]].
  apply find_lock_acquire_from_ge in H2 as ?.
  destruct H as [sb2[SSYMB2 SLOCK]].
  apply find_lock_release_from_ge in H2 as ?.
  destruct H as [sb3[SSYMB3 SUNLOCK]].
  apply find_lock_acquire_from_ge in H3 as ?.
  destruct H as [tb2[TSYMB2 TLOCK]].
  apply find_lock_release_from_ge in H3 as ?.
  destruct H as [tb3[TSYMB3 TUNLOCK]].
  exists nat,lt, (fun a b =>MS sge tge tb sb tb2 sb2 tb3 sb3 sfl tfl).
  constructor.
  apply lt_wf.
  {
    unfold MS;intros;Hsimpl;auto.
    inv H. inv AGMU;auto.
  }
  {
    unfold MS;intros;Hsimpl;auto.
    inv H;auto.
  }
  {
    apply ge_related_ge_lessmatch in H3.
    apply ge_related_ge_lessmatch in H2.
    apply ge_lessmatch_comm in H2.
    eapply ge_lessmatch_trans in H2;eauto.
    destruct H2;constructor;auto.
  }
  {
    intros.
    destruct H as (?&?&?).
    inv H.
    auto.
  }
  {
    unfold speclang;simpl.
    intros.
    
    exploit initsim;try apply H5;eauto.
    intros. Hsimpl.
    Esimpl;eauto.
    intros.
    exists O. eauto.
  }
  {
    unfold speclang;simpl.
    intros.
    eapply match_tau_step in H0;eauto.
    Hsimpl.
    right. Esimpl;eauto.
    constructor;auto.
    destruct H5 as (?&?&?);auto.
  }
  {
    unfold speclang;simpl.
    intros.
    eapply match_external in H0 as ?;eauto.
  }
  {
    unfold speclang;simpl;intros.
    eapply match_afterext in H;eauto.
    Hsimpl. Esimpl;eauto.
  }
  {
    unfold speclang;simpl;intros.
    eapply match_halt in H;eauto.
  }
Qed.