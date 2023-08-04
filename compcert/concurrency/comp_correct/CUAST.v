Require Import Coqlib Integers Maps Errors Values String AST Globalenvs Memory
MemClosures_local LDSimDefs.


(** * general form of compilation unit, similar to AST.program *)

(** A compilation unit consists of:
- a collection of global definitions (name and description);
- a set of public names (the names that are visible outside 
  this compilation unit).

A global definition is either a global function or a global variable.
The type of function descriptions and that of additional information
for variables vary among the various intermediate languages and are
taken as parameters to the [program] type.  The other parts of whole
programs are common to all languages. *)

Record comp_unit_generic (F V: Type) : Type :=
  {
    cu_defs: list (ident * globdef F V);
    cu_public: list ident;
  }.

Arguments cu_defs [F V].
Arguments cu_public [F V].

Definition comp_unit_defmap {F V: Type} (cu: comp_unit_generic F V) : PTree.t (globdef F V) :=
  PTree_Properties.of_list cu.(cu_defs).

Definition cu_to_prog {F V: Type} (cu: comp_unit_generic F V) : AST.program F V :=
  mkprogram (cu_defs cu) (cu_public cu) 1%positive.

Coercion cu_to_prog : comp_unit_generic >-> program.

Lemma comp_unit_defmap_eq:
  forall F V (cu: comp_unit_generic F V),
    comp_unit_defmap cu = prog_defmap cu.
Proof.
  destruct cu. unfold comp_unit_defmap, prog_defmap. auto.
Qed.

(** * general form of global environment, similar to Genv.globalenv, but extend genv_next *)
(** extension of global environment, i.e. extending Genv.genv_next *)
Program Definition ge_extend {F V: Type}
        (ge: Genv.t F V) (bound: block) (GEBOUND: Ple (Genv.genv_next ge) bound)
  : Genv.t F V:=
  @Genv.mkgenv F V (Genv.genv_public ge)
              (Genv.genv_symb ge)
              (Genv.genv_defs ge) bound _ _ _.
Next Obligation.
  exploit Genv.genv_symb_range; eauto. intros. xomega.
Qed.
Next Obligation.
  exploit Genv.genv_defs_range; eauto. intros. xomega.
Qed.
Next Obligation.
  eapply (Genv.genv_vars_inj ge); eauto.
Qed.
  
Inductive globalenv_generic {F V: Type}: comp_unit_generic F V -> Genv.t F V -> Prop :=
| ge_construct:
    forall cu ge bound ge' (GEBOUND: Ple (Genv.genv_next ge) bound),
      ge = Genv.globalenv (mkprogram (cu_defs cu) (cu_public cu) 1%positive) ->
      ge' = ge_extend ge bound GEBOUND ->
      globalenv_generic cu ge'.

Section GENV_GEN_EQ.
  Variables F V: Type.
  Variable cu: comp_unit_generic F V.
  Let ge1 := Genv.globalenv (mkprogram (cu_defs cu) (cu_public cu) 1%positive).
  Variable ge2: Genv.t F V.
  Hypothesis GEGEN: globalenv_generic cu ge2.
  Lemma globalenv_generic_senv_eq:
    Senv.equiv ge1 ge2.
  Proof. inv GEGEN. constructor; auto. Qed.
  Lemma globalenv_generic_senv_eq':
    Senv.equiv ge2 ge1.
  Proof. inv GEGEN. constructor; auto. Qed.
  Lemma globalenv_generic_find_symbol_eq:
    forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.
  Proof. inv GEGEN. auto. Qed.
  Lemma globalenv_generic_find_symbol_eq':
    forall id, Genv.find_symbol ge1 id = Genv.find_symbol ge2 id.
  Proof. inv GEGEN. auto. Qed.
  Lemma globalenv_generic_find_funct_ptr_eq:
    forall b, Genv.find_funct_ptr ge2 b = Genv.find_funct_ptr ge1 b.
  Proof. inv GEGEN. auto. Qed.
    Lemma globalenv_generic_find_funct_ptr_eq':
    forall b, Genv.find_funct_ptr ge1 b = Genv.find_funct_ptr ge2 b.
  Proof. inv GEGEN. auto. Qed.
End GENV_GEN_EQ.
Hint Resolve globalenv_generic_senv_eq
     globalenv_generic_senv_eq'
     globalenv_generic_find_symbol_eq
     globalenv_generic_find_symbol_eq'
     globalenv_generic_find_funct_ptr_eq
     globalenv_generic_find_funct_ptr_eq' : gegen.
Ltac gegen:=
  match goal with
  | |- Senv.equiv ?ge (Genv.globalenv ?p) => eapply globalenv_generic_senv_eq'; eauto
  | |- Senv.equiv (Genv.globalenv ?p) ?ge => eapply globalenv_generic_senv_eq; eauto
  | |- (forall id, Genv.find_symbol ?ge _ = Genv.find_symbol (Genv.globalenv ?p) _) => eapply globalenv_generic_find_symbol_eq; eauto
  | |- (forall id, Genv.find_symbol (Genv.globalenv _) _ = Genv.find_symbol _ _) => eapply globalenv_generic_find_symbol_eq'; eauto
  | |- (forall id, Genv.find_funct_ptr ?ge _ = Genv.find_funct_ptr (Genv.globalenv ?p) _) =>
    eapply globalenv_generic_find_funct_ptr_eq; eauto
  | |- (forall id, Genv.find_funct_ptr (Genv.globalenv _) _ = Genv.find_funct_ptr _ _) =>
    eapply globalenv_generic_find_funct_ptr_eq'; eauto
  end.

Theorem find_def_symbol:
  forall F V (p: comp_unit_generic F V)  id g ge,
    globalenv_generic p ge ->
    (comp_unit_defmap p) ! id = Some g <->
    (exists b, Genv.find_symbol ge id = Some b /\ Genv.find_def ge b = Some g).
Proof.
  intros. inv H. unfold Genv.find_symbol, Genv.find_def; simpl.
  unfold comp_unit_defmap.
  generalize (Genv.find_def_symbol {| prog_defs := cu_defs p; prog_public := cu_public p; prog_main := 1%positive |} id g).
  unfold prog_defmap, Genv.find_symbol, Genv.find_def. simpl. auto.
Qed.

(** TODO: move to cuast *)
Lemma find_def_inversion:
  forall F V (cu: comp_unit_generic F V) ge b g,
    globalenv_generic cu ge ->
    Genv.find_def ge b = Some g ->
    exists id, In (id, g) (cu_defs cu).
Proof.
  clear; intros until g. inversion 1; subst. inv H. inv H1.
  unfold ge_extend. unfold Genv.find_def. simpl.
  unfold Genv.globalenv.
  apply Genv.add_globals_preserves.
  (* preserves *)
  simpl; intros.
  rewrite PTree.gsspec in H1. destruct (peq b (Genv.genv_next ge)).
  inv H1. exists id; auto.
  auto.
  (* base *)
  simpl; intros. rewrite PTree.gempty in H. discriminate.
Qed.

Lemma find_funct_ptr_prop:
  forall F V (P: F -> Prop) (cu: comp_unit_generic F V) ge b f,
    (forall id f', In (id, Gfun f') (cu_defs cu) -> P f') ->
    globalenv_generic cu ge ->
    Genv.find_funct_ptr ge b = Some f -> P f.
Proof.
  clear. 
  unfold Genv.find_funct_ptr; intros.
  destruct (Genv.find_def ge b) eqn:DEF; try discriminate.
  destruct g; inv H1.
  eapply find_def_inversion in DEF; eauto. destruct DEF; eauto.
Qed.

Lemma find_funct_prop:
  forall F V (P: F -> Prop) (cu: comp_unit_generic F V) ge v f,
    (forall id f', In (id, Gfun f') (cu_defs cu) -> P f') ->
    globalenv_generic cu ge ->
    Genv.find_funct ge v = Some f -> P f.
Proof.
  clear. unfold Genv.find_funct. intros.
  destruct v; try discriminate. destruct Ptrofs.eq_dec; try discriminate.
  eapply find_funct_ptr_prop; eauto.
Qed.

(** It seems that we have to declare external global variables as volatile
    with proper init_data (holding spaces) *)


(** * general form of initial memory *)
Record init_mem_generic {F V: Type} (ge: Genv.t F V) (m: mem) : Prop :=
  {
    globdef_initialized: Genv.globals_initialized ge ge m;
    dom_match: Genv.genv_next ge = Mem.nextblock m;
    
    (** is this condition necessary??? why not put it in precondition of init in sim? *)
    reach_closed: reach_closed m (Mem.valid_block m);
  }.

(** * wrapper for initial core *)
Definition generic_init_core {F V core: Type}
           (fundef_init: F -> list val -> option core)
           (ge: Genv.t F V) (fnid: ident) (args: list val) : option core :=
  match Genv.find_symbol ge fnid with
  | Some b =>
    match Genv.find_funct_ptr ge b with
    | Some cfd => fundef_init cfd args
    |_ => None
    end
  | _ => None
  end.

(** get func name of EF_external *)
Definition gd_ef_fun_name {Func V: Type} (gd: globdef (AST.fundef Func) V) : option string :=
  match gd with
  | Gfun fd =>
    match fd with
    | External ef =>
      match ef with
      | EF_external name _ => Some name
      | _ => None
      end
    | _ => None
    end
  | Gvar _ => None
  end.

(** get block from func name *)
Definition invert_block_from_string {Func V: Type} (ge: Genv.t (AST.fundef Func) V) (name: string) : option block :=
  PTree.fold
    (fun res b gd =>
       match gd_ef_fun_name gd with
       | Some name' => if string_dec name name' then Some b else res
       | None => res
       end)
    ge.(Genv.genv_defs) None.

(** get ident from func name *)
Definition invert_symbol_from_string {Func V: Type} (ge: Genv.t (AST.fundef Func) V) (name: string) : option ident :=
  match invert_block_from_string ge name with
  | Some b => Genv.invert_symbol ge b
  | None => None
  end.

Lemma match_genvs_invert_symbol_from_string_preserved:
  forall (F1 V1 F2 V2: Type) (R: globdef (AST.fundef F1) V1 -> globdef (AST.fundef F2) V2 -> Prop) ge1 ge2,
    Genv.match_genvs R ge1 ge2 ->
    (forall gd1 gd2, R gd1 gd2 -> gd_ef_fun_name gd1 = gd_ef_fun_name gd2) ->
    (forall name id, invert_symbol_from_string ge1 name = Some id ->
                invert_symbol_from_string ge2 name = Some id).
Proof.
  clear. intros. destruct H.
  unfold invert_symbol_from_string in *.
  assert (invert_block_from_string ge1 name = invert_block_from_string ge2 name).
  { unfold invert_block_from_string. clear H1.
    generalize mge_defs H0. clear.
    generalize (Genv.genv_defs ge1) (Genv.genv_defs ge2). clear. intros M1 M2 MATCH REL.
    do 2 rewrite Maps.PTree.fold_spec.
    apply Maps.PTree.elements_canonical_order' in MATCH.
    revert MATCH. generalize (Maps.PTree.elements M1) (Maps.PTree.elements M2) (@None positive). clear M1 M2.
    induction l; intro l'; intros.
    inv MATCH. auto.
    inv MATCH. destruct a as [id1 gd1]; destruct b1 as [id2 gd2].
    destruct H1. simpl in H, H0. subst id2. simpl. apply REL in H0. rewrite H0.
    apply IHl. auto.
  }
  rewrite H in H1. destruct (invert_block_from_string ge2 name) eqn:BLOCK; auto. clear BLOCK H.
  apply Genv.invert_find_symbol in H1. unfold Genv.find_symbol in H1. 
  rewrite <- mge_symb in H1. apply Genv.find_invert_symbol. auto.
Qed.


(** * general form of matching compilation units *)
(** rewrite match_globdef (originally in Linking.v)*)
Section MATCH_CUNIT_GENERIC.

Context {F1 V1 F2 V2: Type}.
Variable match_fundef: F1 -> F2 -> Prop.
Variable match_varinfo: V1 -> V2 -> Prop.

Inductive match_globvar: globvar V1 -> globvar V2 -> Prop :=
| match_globvar_intro: forall i1 i2 init ro vo,
    match_varinfo i1 i2 ->
    match_globvar (mkglobvar i1 init ro vo) (mkglobvar i2 init ro vo).

Inductive match_globdef : globdef F1 V1 -> globdef F2 V2 -> Prop :=
| match_globdef_fun: forall f1 f2,
    match_fundef f1 f2 ->
    match_globdef (Gfun f1) (Gfun f2)
| match_globdef_var: forall v1 v2,
    match_globvar v1 v2 ->
    match_globdef (Gvar v1) (Gvar v2).

Definition match_ident_globdef
           (ig1: ident * globdef F1 V1) (ig2: ident * globdef F2 V2) : Prop :=
  fst ig1 = fst ig2 /\ match_globdef (snd ig1) (snd ig2).

Definition match_comp_unit_gen (cu1: comp_unit_generic F1 V1) (cu2: comp_unit_generic F2 V2) : Prop :=
  list_forall2 (match_ident_globdef) cu1.(cu_defs) cu2.(cu_defs)
  /\ cu2.(cu_public) = cu1.(cu_public).

Theorem match_comp_unit_defmap:
  forall cu1 cu2, match_comp_unit_gen cu1 cu2 ->
  forall id, option_rel match_globdef (comp_unit_defmap cu1)!id (comp_unit_defmap cu2)!id.
Proof.
  intros. apply PTree_Properties.of_list_related. apply H. 
Qed.

End MATCH_CUNIT_GENERIC.


(** * general form of transformation *)
Local Open Scope error_monad_scope.

Section TRANSF_CUNIT_GEN.
Variables A B V W: Type.
Variable transf_fun: ident -> A -> res B.
Variable transf_var: ident -> V -> res W.

Definition transform_partial_cunit2 (p: comp_unit_generic A V) : res (comp_unit_generic B W) :=
  do gl' <- transf_globdefs transf_fun transf_var p.(cu_defs);
    OK {| cu_defs := gl';  cu_public := p.(cu_public) |}.

End TRANSF_CUNIT_GEN.


Section TRANSF_PARTIAL_CUNIT.
Variable A B V: Type.
Variable transf_fun: A -> res B.

Definition transform_partial_cunit (p: comp_unit_generic A V) : res (comp_unit_generic B V) :=
  transform_partial_cunit2 _ _ _ _ (fun i f => transf_fun f) (fun i v => OK v) p.

End TRANSF_PARTIAL_CUNIT.


(** Relation between the program transformation functions from [AST]
  and the [match_program] predicate. *)

Theorem match_transform_partial_cunit2:
  forall {F1 V1 F2 V2: Type}
    (match_fundef: F1 -> F2 -> Prop)
    (match_varinfo: V1 -> V2 -> Prop)
    (transf_fun: ident -> F1 -> res F2)
    (transf_var: ident -> V1 -> res V2)
    (p: comp_unit_generic F1 V1) (tp: comp_unit_generic F2 V2),
    transform_partial_cunit2 _ _ _ _ transf_fun transf_var p = OK tp ->
    (forall i f tf, transf_fun i f = OK tf -> match_fundef f tf) ->
    (forall i v tv, transf_var i v = OK tv -> match_varinfo v tv) ->
    match_comp_unit_gen match_fundef match_varinfo p tp.
Proof.
  unfold transform_partial_cunit2; intros. monadInv H.
  red; simpl; split; auto. 
  revert x EQ. generalize (cu_defs p). 
  induction l as [ | [i g] l]; simpl; intros.
  - monadInv EQ. constructor.
  - destruct g as [f|v].
    + destruct (transf_fun i f) as [tf|?] eqn:TF; monadInv EQ. 
      constructor; auto. split; simpl; auto. econstructor. eauto. 
    + destruct (transf_globvar transf_var i v) as [tv|?] eqn:TV; monadInv EQ.
      constructor; auto. split; simpl; auto. constructor.
      monadInv TV. destruct v; simpl; constructor. eauto.
Qed.

(** The following two theorems are simpler versions for the case where the
  function transformation does not depend on the compilation unit. *)

Theorem match_transform_partial_cunit:
  forall {A B V: Type} (transf_fun: A -> res B)
    (p: comp_unit_generic A V) (tp: comp_unit_generic B V),
    transform_partial_cunit _ _ _ transf_fun p = OK tp ->
    match_comp_unit_gen (fun f tf => transf_fun f = OK tf) eq p tp.
Proof.
  intros.
  eapply match_transform_partial_cunit2. eexact H.
  auto.
  simpl; intros. congruence.
Qed.

Lemma match_cu_match_genv:
  forall F1 V1 F2 V2 match_fundef match_varinfo cu1 cu2 ge1 ge2,
    @match_comp_unit_gen F1 V1 F2 V2 match_fundef match_varinfo cu1 cu2 ->
    globalenv_generic cu1 ge1 ->
    globalenv_generic cu2 ge2 ->
    Genv.genv_next ge1 = Genv.genv_next ge2 ->
    Genv.match_genvs (match_globdef match_fundef match_varinfo) ge1 ge2.
Proof.
  clear. intros. destruct cu1, cu2.
  inv H. inv H0. inv H1. simpl in *. subst bound0 cu_public0.
  eapply Genv.add_globals_match in H3.
  Focus 2.
  instantiate (1:= Genv.empty_genv F2 V2 cu_public1).
  instantiate (1:= Genv.empty_genv F1 V1 cu_public1).
  constructor; auto. simpl. intros. do 2 rewrite Maps.PTree.gempty. constructor.
  constructor; unfold ge_extend; simpl; inv H3; auto.
Qed.

Lemma match_cu_senv_preserved:
  forall F1 V1 F2 V2 match_fundef match_varinfo cu1 cu2 ge1 ge2,
    @match_comp_unit_gen F1 V1 F2 V2 match_fundef match_varinfo cu1 cu2 ->
    globalenv_generic cu1 ge1 ->
    globalenv_generic cu2 ge2 ->
    Genv.genv_next ge1 = Genv.genv_next ge2 ->  
    Senv.equiv ge1 ge2.
Proof.
  intros. exploit match_cu_match_genv; eauto. intro.
  inv H0; inv H1. inv H3. simpl in *. subst. 
  constructor; simpl; intros.
  unfold Genv.find_symbol, ge_extend; simpl. auto.
  split; intros.
  unfold Genv.public_symbol, Genv.genv_public, Genv.find_symbol. rewrite mge_symb. simpl.
  match goal with
  | |- match ?x with _ => _ end = match ?x with _ => _ end =>
    destruct x eqn:?; try congruence
  end.
  unfold Genv.globalenv, ge_extend; simpl.
  inv H. rewrite H1.
  do 2 rewrite Genv.genv_public_add_globals. simpl. auto.
  unfold Genv.block_is_volatile, Genv.find_var_info, Genv.find_def.
  unfold ge_extend; simpl.
  destruct (mge_defs b); auto. inv H0; auto. inv H1; auto.
Qed.

Lemma match_cu_ge_match:
  forall F1 V1 F2 V2 match_fundef match_varinfo cu1 cu2 (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2),
    @match_comp_unit_gen F1 V1 F2 V2 match_fundef match_varinfo cu1 cu2 ->
    globalenv_generic cu1 ge1 ->
    globalenv_generic cu2 ge2 ->
    Genv.genv_next ge1 = Genv.genv_next ge2 ->
    LDSimDefs.ge_match ge1 ge2.
Proof.
  intros.
  exploit match_cu_match_genv; eauto.
  inv H0; auto. inv H1; auto. intros [? ? ?].
  constructor; auto.
  * intro id. unfold ge_extend; simpl.
    do 2 rewrite Genv.globalenv_public; simpl. inv H. rewrite H1. tauto.
  * intro. unfold ge_extend; simpl. rewrite mge_symb. tauto.
  * intros. unfold ge_extend; simpl. rewrite mge_symb in H1. rewrite H0 in H1. inv H1.
    specialize (mge_defs b'). inv mge_defs; constructor.
    inv H4; constructor. inv H5. constructor.
Qed.

Require Import LDSim_local.
Lemma match_cu_ge_match_strict:
  forall F1 V1 F2 V2 match_fundef match_varinfo cu1 cu2 (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2),
    @match_comp_unit_gen F1 V1 F2 V2 match_fundef match_varinfo cu1 cu2 ->
    globalenv_generic cu1 ge1 ->
    globalenv_generic cu2 ge2 ->
    Genv.genv_next ge1 = Genv.genv_next ge2 ->
    ge_match_strict ge1 ge2.
Proof.
  intros.
  exploit match_cu_match_genv; eauto.
  inv H0; auto. inv H1; auto. intros [? ? ?].
  constructor; auto.
  * intro id. unfold ge_extend; simpl.
    do 2 rewrite Genv.globalenv_public; simpl. inv H. rewrite H1. tauto.
  * intros. unfold ge_extend; simpl. rewrite mge_symb in H1. rewrite H0 in H1. inv H1.
    specialize (mge_defs b'). inv mge_defs; constructor.
    inv H4; constructor. inv H5. constructor.
Qed.




(** relating local ge *)
Import Blockset.
Inductive ge_related {F V: Type} (ge ge_local: Genv.t F V) : Prop :=
  GE_RELATED: forall j : Bset.inj,
    (** domain *)
    (forall b b', j b = Some b' -> exists gd, (Genv.genv_defs ge_local) ! b = Some gd) ->
    (** injective *)
    (forall b1 b2 b', j b1 = Some b' -> j b2 = Some b' -> b1 = b2) ->
    (** public eq *)
    (Genv.genv_public ge = Genv.genv_public ge_local) ->
    (** symb related *)
    (forall id, inj_oblock j (Genv.find_symbol ge_local id) (Genv.find_symbol ge id)) ->
    (** defs related *)
    (forall b gd, (Genv.genv_defs ge_local) ! b = Some gd -> exists b', j b = Some b') ->
    (forall b' gd', (Genv.genv_defs ge) ! b' = Some gd' -> exists b, j b = Some b') ->
    (forall b b', j b = Some b' -> (Genv.genv_defs ge_local) ! b = (Genv.genv_defs ge) ! b') ->
    (** genv_next *)
    Ple (Genv.genv_next ge_local) (Genv.genv_next ge) ->
    ge_related ge ge_local.

Require GMemory FMemory.
Require Import Integers Floats FMemPerm.

Definition read_as_zero_fm {F V: Type} (ge: Genv.t F V)
           (m: FMemory.Mem.mem) (b: block) (ofs len: Z) : Prop :=
  forall chunk p,
  ofs <= p -> p + size_chunk chunk <= ofs + len ->
  (align_chunk chunk | p) ->
  FMemory.Mem.load chunk m b p =
  Some (match chunk with
        | Mint8unsigned | Mint8signed | Mint16unsigned | Mint16signed | Mint32 => Vint Int.zero
        | Mint64 => Vlong Int64.zero
        | Mfloat32 => Vsingle Float32.zero
        | Mfloat64 => Vfloat Float.zero
        | Many32 | Many64 => Vundef
        end).

Fixpoint load_store_init_data_fm {F V: Type} (ge: Genv.t F V)
         (m: FMemory.Mem.mem) (b: block) (p: Z) (il: list init_data) {struct il} : Prop :=
  match il with
  | nil => True
  | Init_int8 n :: il' =>
    FMemory.Mem.load Mint8unsigned m b p = Some(Vint(Int.zero_ext 8 n))
    /\ load_store_init_data_fm ge m b (p + 1) il'
  | Init_int16 n :: il' =>
    FMemory.Mem.load Mint16unsigned m b p = Some(Vint(Int.zero_ext 16 n))
    /\ load_store_init_data_fm ge m b (p + 2) il'
  | Init_int32 n :: il' =>
    FMemory.Mem.load Mint32 m b p = Some(Vint n)
    /\ load_store_init_data_fm ge m b (p + 4) il'
  | Init_int64 n :: il' =>
    FMemory.Mem.load Mint64 m b p = Some(Vlong n)
    /\ load_store_init_data_fm ge m b (p + 8) il'
  | Init_float32 n :: il' =>
    FMemory.Mem.load Mfloat32 m b p = Some(Vsingle n)
    /\ load_store_init_data_fm ge m b (p + 4) il'
  | Init_float64 n :: il' =>
    FMemory.Mem.load Mfloat64 m b p = Some(Vfloat n)
    /\ load_store_init_data_fm ge m b (p + 8) il'
  | Init_addrof symb ofs :: il' =>
    (exists b', Genv.find_symbol ge symb = Some b' /\ FMemory.Mem.load Mptr m b p = Some(Vptr b' ofs))
    /\ load_store_init_data_fm ge m b (p + size_chunk Mptr) il'
  | Init_space n :: il' =>
    read_as_zero_fm ge m b p n
    /\ load_store_init_data_fm ge m b (p + Zmax n 0) il'
  end.

Definition globals_initialized_fmem {F V: Type} (ge: Genv.t F V) (fm: FMemory.Mem.mem) : Prop :=
  forall b gd,
    Genv.find_def ge b = Some gd ->
    match gd with
    | Gfun _ =>
      FMemory.Mem.perm fm b 0 Memperm.Cur Memperm.Nonempty /\
      (forall ofs k p, FMemory.Mem.perm fm b ofs k p -> ofs = 0 /\ p = Memperm.Nonempty)
    | Gvar v =>
      FMemory.Mem.range_perm fm b 0 (init_data_list_size (gvar_init v)) Memperm.Cur (permission_convert (Genv.perm_globvar v))
      /\
      (forall ofs k p,
          FMemory.Mem.perm fm b ofs k p ->
          0 <= ofs < init_data_list_size (gvar_init v)
          /\ Memperm.perm_order (permission_convert (Genv.perm_globvar v)) p)
      /\
      (gvar_volatile v = false -> load_store_init_data_fm ge fm b 0 (gvar_init v))
      /\
      (gvar_volatile v = false ->
       FMemory.Mem.loadbytes fm b 0 (init_data_list_size (gvar_init v)) = Some (Genv.bytes_of_init_data_list ge (gvar_init v)))
    end.
      

Record init_fmem_generic {F V: Type} (ge: Genv.t F V) (m: FMemory.Mem.mem) : Prop :=
  { globdef_initialized_fm : globals_initialized_fmem ge m;
    dom_match_fm : forall b, Plt b (Genv.genv_next ge) <-> FMemory.Mem.valid_block m b;
    reach_closed_fm : MemClosures.reach_closed (FMemory.strip m) (FMemory.Mem.valid_block m) }.

Definition init_gmem_generic {F V: Type} (ge: Genv.t F V) (gm: GMemory.gmem) : Prop :=
  exists fm, FMemory.strip fm = gm /\ init_fmem_generic ge fm.


Fixpoint is_internal {F V: Type} (cu_defs: list (ident * globdef (AST.fundef F) V)) (id: ident) : bool :=
  match cu_defs with
  | (id', gdef) :: cu_defs' =>
    if (ident_eq id id') then
      match gdef with
      | Gfun (Internal _) => true
      | _ => is_internal cu_defs' id
      end
    else is_internal cu_defs' id
  | nil => false
  end.

Definition transf_func_correct {F1 F2: Type} (transf_fun: ident -> AST.fundef F1 -> res (AST.fundef F2)) : Prop :=
  forall id f1 f2, transf_fun id f1 = OK f2 ->
              match f1, f2 with
              | Internal _, Internal _ => True
              | External _, External _ => True
              | _, _ => False
              end.
    
Lemma is_internal_preserved:
  forall A B V W defs1 defs2 transf_fun transf_var,
    @transf_func_correct A B transf_fun ->
    transf_globdefs transf_fun transf_var defs1 = OK defs2 ->
    (forall id, @is_internal A V defs1 id = @is_internal B W defs2 id).
Proof.
  intros until 1. revert defs2. induction defs1.
  intros. monadInv H0. auto.
  destruct defs2 as [|b defs2]; intros; try monadInv H0.
  simpl in H0. destruct a, g. destruct transf_fun. monadInv H0. discriminate.
  destruct transf_globvar. monadInv H0. discriminate.
  simpl in *. destruct a. destruct g. destruct transf_fun eqn:TRANSF.
  destruct f, f0; eapply H in TRANSF; try contradiction;
    monadInv H0; destruct ident_eq; auto.
  discriminate.
  destruct transf_globvar; monadInv H0.
  destruct ident_eq; auto.
Qed.

Definition internal_fn {F V} (cu: comp_unit_generic (AST.fundef F) V): list ident :=
  filter (is_internal (cu_defs cu)) (cu_public cu).

Lemma transform_partial_cunit2_internal_fn_preserved:
  forall F1 V1 F2 V2 cu1 cu2 transf_fun transf_var,
    transform_partial_cunit2 _ _ V1 V2 transf_fun transf_var cu1 = OK cu2 ->
    transf_func_correct transf_fun ->
    @internal_fn F1 V1 cu1 = @internal_fn F2 V2 cu2.
Proof.
  unfold transform_partial_cunit2, internal_fn.
  destruct cu1, cu2. simpl. intros. monadInv H.
  pose proof (is_internal_preserved _ _ _ _ _ _ _ _ H0 EQ). clear H0 EQ.
  induction cu_public1; simpl; auto.
  rewrite H. destruct is_internal; auto. f_equal. auto.
Qed.





Lemma load_store_init_data_preserved:
  forall F1 V F2 transf_fun ge1 ge2 m b init,
    Genv.match_genvs (match_globdef (fun (f : F1) (tf : F2) => transf_fun f = OK tf) (@eq V))
                     ge1 ge2 ->
    Genv.load_store_init_data ge1 m b 0 init <->
    Genv.load_store_init_data ge2 m b 0 init.
Proof.
  intros until 1. generalize 0. induction init; intros.
  tauto. simpl in *. destruct a; try rewrite IHinit; try (split; intro; tauto).
  split; intros []; destruct H0 as [b' [FIND LOAD]]; split; auto.
  exists b'. split; auto. inv H. unfold Genv.find_symbol. rewrite mge_symb. auto.
  exists b'. split; auto. inv H. unfold Genv.find_symbol. rewrite <- mge_symb. auto.
Qed.


Lemma bytes_of_init_data_list_preserved:
  forall F1 V F2 transf_fun ge1 ge2 init,
    Genv.match_genvs (match_globdef (fun (f : F1) (tf : F2) => transf_fun f = OK tf) (@eq V))
                     ge1 ge2 ->
    (Genv.bytes_of_init_data_list ge2 init) =
    (Genv.bytes_of_init_data_list ge1 init).
Proof.
  intros until 1. induction init; simpl; auto.
  rewrite IHinit. f_equal.
  destruct a; simpl; auto.
  unfold Genv.find_symbol. inv H. rewrite mge_symb. auto.
Qed.

Lemma init_mem_preserved:
  forall F1 V F2 transf_fun cu1 cu2 ge1 ge2 m,
    transform_partial_cunit F1 F2 V transf_fun cu1 = OK cu2 ->
    globalenv_generic cu1 ge1 ->
    globalenv_generic cu2 ge2 ->
    Genv.genv_next ge1 = Genv.genv_next ge2 ->
    init_mem_generic ge1 m ->
    init_mem_generic ge2 m.
Proof.
  intros. apply match_transform_partial_cunit in H.
  eapply match_cu_match_genv in H; eauto. pose proof H as MATCH. inv H.
  inv H3; constructor; try congruence.
  unfold Genv.globals_initialized in *. intros b gd FIND.
  specialize (mge_defs b). 
  unfold Genv.find_def in FIND. rewrite FIND in mge_defs. inv mge_defs.
  symmetry in H. specialize (globdef_initialized0 b x H).
  inv H4; auto. inv H3; simpl in *.
  repeat (split; try tauto). 
  intro. erewrite <- load_store_init_data_preserved; eauto. tauto.
  erewrite bytes_of_init_data_list_preserved; eauto. tauto.
Qed.

Lemma init_mem_preserved':
  forall F1 V F2 transf_fun cu1 cu2 ge1 ge2 m,
    transform_partial_cunit F1 F2 V transf_fun cu1 = OK cu2 ->
    globalenv_generic cu1 ge1 ->
    globalenv_generic cu2 ge2 ->
    Genv.genv_next ge1 = Genv.genv_next ge2 ->
    init_mem_generic ge2 m ->
    init_mem_generic ge1 m.
Proof.
  intros. apply match_transform_partial_cunit in H.
  eapply match_cu_match_genv in H; eauto. pose proof H as MATCH. inv H.
  inv H3; constructor; try congruence.
  unfold Genv.globals_initialized in *. intros b gd FIND.
  specialize (mge_defs b). 
  unfold Genv.find_def in FIND. rewrite FIND in mge_defs. inv mge_defs.
  symmetry in H3. specialize (globdef_initialized0 b y H3).
  inv H4; auto. inv H; simpl in *.
  repeat (split; try tauto). 
  intro. eapply load_store_init_data_preserved; eauto. tauto.
  erewrite <- bytes_of_init_data_list_preserved; eauto. tauto.
Qed.





(** CU property: no dup ident, no dup ef names *)
Fixpoint nodup_ident (ids: list AST.ident) : bool :=
  match ids with
  | nil => true
  | id :: ids' => if in_dec peq id ids' then false else nodup_ident ids'
  end.

Lemma nodup_ident_correct:
  forall ids, nodup_ident ids = true -> NoDup ids.
Proof.
  induction ids; intros. constructor. 
  simpl in H. destruct in_dec; try discriminate.
  constructor; auto.
Qed.

Definition nodup_gd_ident {F V: Type} (cudefs: list (ident * globdef F V)) : bool :=
  nodup_ident (map fst cudefs).

Lemma nodup_gd_ident_no_repet:
  forall F V (cudefs: list (ident * globdef F V)),
    nodup_gd_ident cudefs = true ->
    list_norepet (map fst cudefs).
Proof.
  induction cudefs; intros. constructor.
  simpl in *. unfold nodup_gd_ident in H. simpl in H.
  destruct in_dec; try discriminate. constructor; auto.
Qed.
  

Lemma norepet_defs_gd_ident_exists:
  forall F V (cu: comp_unit_generic F V),
    let ge := Genv.globalenv cu in
    list_norepet (map fst (cu_defs cu)) ->
    forall b gd,
      PTree.get b (Genv.genv_defs ge) = Some gd ->
      exists id, PTree.get id (Genv.genv_symb ge) = Some b.
Proof.
  intros until ge. destruct cu; simpl. intro NOREPET.
  subst ge. unfold Genv.globalenv. simpl. revert NOREPET.
  replace cu_defs0 with (rev (rev cu_defs0)); try apply rev_involutive.
  generalize (rev cu_defs0). clear cu_defs0. intro rcu_defs.
  induction (rcu_defs); intros; simpl in H.
  rewrite PTree.gempty in H. discriminate.
  rewrite map_rev in NOREPET. simpl in NOREPET.
  apply list_norepet_append_commut in NOREPET. simpl in NOREPET. inv NOREPET.
  rewrite <-map_rev in H3. specialize (IHl H3). simpl.
  rewrite Genv.add_globals_app in H. 
  rewrite Genv.add_globals_app. simpl in *.
  destruct (peq b (Genv.genv_next (Genv.add_globals (Genv.empty_genv F V cu_public0) (rev l)))).
  subst. exists (fst a). rewrite PTree.gss. auto.
  rewrite PTree.gso in H; auto. pose proof H. apply IHl in H. destruct H.
  exists x. rewrite PTree.gso; auto. intro. subst.
  exploit (Genv.find_symbol_inversion (Build_comp_unit_generic _ _ (rev l) cu_public0)).
  unfold Genv.globalenv. simpl. eauto.
  unfold prog_defs_names. simpl. rewrite map_rev. auto.
Qed.

Lemma nodup_gd_ident_exists:
  forall F V cu,
    @nodup_gd_ident F V (cu_defs cu) = true ->
    let ge := Genv.globalenv cu in
    forall b gd,
      PTree.get b (Genv.genv_defs ge) = Some gd ->
      exists id, PTree.get id (Genv.genv_symb ge) = Some b.
Proof. intros until 1. apply norepet_defs_gd_ident_exists. apply nodup_gd_ident_no_repet. auto. Qed.


Lemma nodup_gd_init_genv_ident_exists:
  forall F V cu ge,
    @nodup_gd_ident F V (cu_defs cu) = true ->
    globalenv_generic cu ge ->
    forall b gd,
      PTree.get b (Genv.genv_defs ge) = Some gd ->
      exists id, PTree.get id (Genv.genv_symb ge) = Some b.
Proof. intros until 2. inv H0. simpl. apply nodup_gd_ident_exists. auto. Qed.


Lemma nodup_gd_init_genv_ident_exists':
  forall F V cu ge,
    @nodup_gd_ident F V (cu_defs cu) = true ->
    globalenv_generic cu ge ->
    forall b gd,
      Genv.find_def ge b = Some gd ->
      exists id, In (id, gd) (cu_defs cu) /\
            Genv.find_symbol ge id = Some b.
Proof.
  intros. exploit nodup_gd_init_genv_ident_exists; eauto.
  intros [id FINDSYMB].
  exists id. split; auto. inv H0. unfold Genv.find_def in H1. simpl in *.
  assert ((prog_defmap cu)! id = Some gd).
  apply Genv.find_def_symbol. eauto.
  eapply in_prog_defmap in H0. auto.
Qed.

(** need a stronger pre condition on genv_defs: no rep in gds *)
Fixpoint ef_name_notin {F V: Type} (name: string) (ids: list (AST.ident * (AST.globdef (AST.fundef F) V))) : bool :=
  match ids with
  | nil => true
  | (id, gd) :: ids' =>
    match gd_ef_fun_name gd with
    | Some name' => if string_dec name name' then false
                   else ef_name_notin name ids'
    | _ => ef_name_notin name ids'
    end
  end.

Lemma ef_name_notin_correct:
  forall F V name defs,
    @ef_name_notin F V  name defs = true ->
    forall id gd name',
      In (id,gd) defs ->
      gd_ef_fun_name gd = Some name' ->
      name <> name'.
Proof.
  induction defs; simpl; intros. contradiction.
  destruct a. destruct g. destruct f. simpl in *. inv H0. inv H2. discriminate.
  eapply IHdefs; eauto.
  destruct gd_ef_fun_name eqn:NAME. destruct string_dec. discriminate.
  inv H0. inv H2. rewrite NAME in H1. inv H1. auto. eapply IHdefs; eauto.
  inv H0. inv H2. congruence. eapply IHdefs; eauto.
  destruct gd_ef_fun_name eqn:NAME. destruct string_dec; try congruence.
  inv H0. inv H2. congruence. eapply IHdefs; eauto.
  inv H0. inv H2. congruence. eapply IHdefs; eauto.
Qed.

Fixpoint nodup_ef {F V: Type} (ids: list (AST.ident * AST.globdef (AST.fundef F) V)) : bool :=
  match ids with
  | nil => true
  | (id, gd) :: ids' =>
    match gd_ef_fun_name gd with
    | Some name => ef_name_notin name ids' && nodup_ef ids'
    | None => nodup_ef ids'
    end
  end.

Lemma nodup_ef_correct:
  forall F V ids,
    @nodup_ef F V  ids = true ->
    forall n1 n2 id1 gd1 id2 gd2 name1 name2,
      n1 <> n2 ->
      nth_error ids n1 = Some (id1, gd1) ->
      nth_error ids n2 = Some (id2, gd2) ->
      gd_ef_fun_name gd1 = Some name1 ->
      gd_ef_fun_name gd2 = Some name2 ->
      name1 <> name2.
Proof.
  induction ids; simpl; intros.
  rewrite nth_error_nil in H1; discriminate.
  destruct n1, n2; simpl in *; auto. 
  { inv H1. apply nth_error_in in H2.
    rewrite H3 in H.
    intro. inv H1. apply andb_true_iff in H. destruct H.
    eapply ef_name_notin_correct in H2; try exact H; eauto. }
  { inv H2. apply nth_error_in in H1.
    rewrite H4 in H.
    intro. inv H2. apply andb_true_iff in H. destruct H.
    eapply ef_name_notin_correct in H1; try exact H; eauto. }
  rewrite Nat.succ_inj_wd_neg in H0.
  destruct a; eauto. destruct gd_ef_fun_name. apply andb_true_iff in H. destruct H.
  eauto. eauto.
Qed.

Lemma fold_in:
  forall A B (func: A -> option B) al ob b,
    fold_left (fun ob a => if func a then func a else ob) al ob = Some b ->
    (exists a, In a al /\ func a = Some b) \/ (ob = Some b).
Proof.
  induction al; intros. auto.
  simpl in H. destruct (func a) eqn: FUNC; simpl in H.
  left. apply IHal in H. destruct H as [[a' [IN FUNC']] | DEFAULT].
  exists a'. split; simpl; auto. inv DEFAULT. exists a. simpl. auto.
  apply IHal in H. destruct H as [[a' [IN FUNC']] | DEFAULT].
  left. exists a'. simpl; auto. auto.
Qed.

Lemma fold_in':
  forall A B (func: A -> option B) al ob b a,
    In a al -> func a = Some b ->
    exists b', fold_left (fun ob a => if func a then func a else ob) al ob = Some b'.
Proof.
  induction al; simpl; intros. contradiction.
  destruct H.
  subst. rewrite H0. clear. revert b. induction al; simpl. eauto. destruct (func a); eauto.
  destruct (func a). clear. revert b0. induction al; simpl. eauto. destruct (func a); eauto.
  eauto.
Qed.

  
Definition norep_ef_name {F V: Type} (ge: Genv.t (AST.fundef F) V) : Prop :=
   forall b b' gd gd' name name',
        b <> b' ->
        Genv.find_def ge b = Some gd ->
        Genv.find_def ge b' = Some gd' ->
        gd_ef_fun_name gd = Some name ->
        gd_ef_fun_name gd' = Some name' ->
        name <> name'.

Lemma nodup_ef_ge_norep_ef_name:
  forall F V cu,
    nodup_gd_ident (cu_defs cu) = true ->
    @nodup_ef F V (cu_defs cu) = true ->
    forall ge: Genv.t (AST.fundef F) V,
      globalenv_generic cu ge ->
      norep_ef_name ge.
Proof.
  intros. pose proof H1 as GEINIT. inv H1. 
  intros. intros b1 b2 gd1 gd2 name1 name2 NEQ FIND1 FIND2 NAME1 NAME2.
  exploit nodup_gd_init_genv_ident_exists'; try exact FIND1; eauto. intros [id1 [IN1 FIND1']].
  exploit nodup_gd_init_genv_ident_exists'; try exact FIND2; eauto. intros [id2 [IN2 FIND2']].
  unfold Genv.find_def in *. simpl in *.
  assert (id1 <> id2).
  { intro. apply NEQ. congruence. }
  apply In_nth_error in IN1. destruct IN1 as [n1 IN1].
  apply In_nth_error in IN2. destruct IN2 as [n2 IN2].
  assert (n1 <> n2). intro. subst. apply H1. congruence.
  eapply nodup_ef_correct; eauto.
Qed.
  

Lemma invert_block_from_string_eq:
  forall F V (ge ge_local: Genv.t (AST.fundef F) V)
    (NOREPEF: norep_ef_name ge_local),
    (forall b gd, (Genv.genv_defs ge_local) ! b = Some gd -> exists id, (Genv.genv_symb ge_local) ! id = Some b) ->
    ge_related ge ge_local ->
    forall name, option_rel (fun b b' => exists id, Genv.find_symbol ge id = Some b /\ Genv.find_symbol ge_local id = Some b')
                       (invert_block_from_string ge name)
                       (invert_block_from_string ge_local name).
Proof.
  intros. unfold invert_block_from_string.
  remember (fun p : positive * globdef (AST.fundef F) V =>
              match gd_ef_fun_name (snd p) with
              | Some name' => if String.string_dec name name' then Some (fst p) else None
              | None => None
              end) as FILTER.
  assert ((fun ob a => if FILTER a then FILTER a else ob) =
          (fun a p => match gd_ef_fun_name (snd p) with
                   | Some name' => if String.string_dec name name' then Some (fst p) else a
                   | None => a
                   end)).
  { subst. do 2 (apply Axioms.functional_extensionality; intro).
    destruct x0. destruct g; simpl; auto. destruct f; auto.
    destruct e; auto. destruct String.string_dec; auto. }
  repeat rewrite PTree.fold_spec. rewrite <- H1 in *. clear H1. rename HeqFILTER into HFUNC.
  destruct (fold_left) eqn:FOLD.
  apply fold_in in FOLD. destruct FOLD as [[[b [f|v]] [IN NAME]]|C]; try discriminate. 
  2: subst; simpl in *; discriminate.
  rewrite HFUNC in NAME. simpl in NAME.
  destruct f; try discriminate. destruct e; try discriminate. destruct String.string_dec; try discriminate.
  inversion NAME. subst name0 p. clear NAME.
  apply PTree.elements_complete in IN.
  destruct H0. exploit H5. eauto. intros [b' INJ]. exploit H0. eauto. intros [gd' DEF].
  exploit H6. eauto. rewrite DEF, IN. intro A. inversion A. subst gd'. clear A.
  destruct fold_left eqn:FOLD'.
  apply fold_in in FOLD'. destruct FOLD' as [[[b'' [f'|v']] [IN' NAME']]|C]; try discriminate. 
  2: subst; simpl in *; discriminate.
  rewrite HFUNC in NAME'. simpl in NAME'.
  destruct f'; try discriminate. destruct e; try discriminate. destruct String.string_dec; try discriminate.
  inversion NAME'. subst name0 p. clear NAME'.
  assert (b'' = b').
  { apply PTree.elements_complete in IN'. revert DEF IN' NOREPEF; clear; intros.
    destruct (peq b' b''); auto.
    exploit NOREPEF; eauto; simpl; eauto. contradiction.
  }
  subst b''. exploit H. eauto. intros[id FIND].
  specialize (H3 id). unfold Genv.find_symbol in *. rewrite FIND in H3. inversion H3.
  rewrite INJ in H11. inversion H11. subst bj b0 b'0. clear H11.
  constructor. exists id. auto.
  
  exfalso. apply PTree.elements_correct in DEF.
  eapply fold_in' in DEF. rewrite FOLD' in DEF. destruct DEF. discriminate.
  subst. simpl. destruct String.string_dec; try contradiction; eauto.

  destruct (fold_left _ (PTree.elements (Genv.genv_defs ge_local)) None) eqn:FOLD';[|constructor].
  exfalso.
  apply fold_in in FOLD'. destruct FOLD' as [[[b'' [f'|v']] [IN' NAME']]|C]; try discriminate. 
  2: subst; simpl in *; discriminate.
  rewrite HFUNC in NAME'. simpl in NAME'.
  destruct f'; try discriminate. destruct e; try discriminate. destruct String.string_dec; try discriminate.
  inversion NAME'. subst name0 p. clear NAME'.
  apply PTree.elements_complete in IN'.
  destruct H0. exploit H4. eauto. intros [b INJ]. exploit H6. eauto.
  rewrite IN'. intro A. symmetry in A. eapply PTree.elements_correct in A. eapply fold_in' in A.
  rewrite FOLD in A. destruct A; discriminate.
  subst; simpl. destruct String.string_dec; try contradiction; eauto.
Qed.














Lemma transform_partial_cunit_init_genv_preserved:
  forall F1 V1 F2 V2 cu1 cu2 transf_fun transf_var,
    transform_partial_cunit2 F1 V1 F2 V2 transf_fun transf_var cu1 = OK cu2 ->
    forall ge1, globalenv_generic cu1 ge1 ->
           exists ge2, globalenv_generic cu2 ge2 /\
                  Genv.genv_next ge2 = Genv.genv_next ge1.
Proof.
  intros. inv H0.
  assert (Ple (Genv.genv_next (Genv.globalenv cu2)) bound).
  { eapply (match_transform_partial_cunit2 (fun f tf => exists i, transf_fun i f = OK tf)
                                           (fun v tv => exists i, transf_var i v = OK tv)) in H; eauto.
    destruct cu1, cu2. inv H. simpl in *. unfold Genv.globalenv in *.
    eapply Genv.add_globals_match in H0; eauto.
    inv H0. rewrite mge_next. eauto.
    constructor; auto. simpl. intros. do 2 rewrite Maps.PTree.gempty. constructor.
  }
  exists (ge_extend (Genv.globalenv cu2) bound H0).
  split; auto. econstructor; eauto.
Qed.
