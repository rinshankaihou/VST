(* This file is partly adapted from Compositional CompCert:
   - The interaction semantics [Language] is adapted from 
   [semantics.v] and [effect_semantics.v] in Compositional CompCert.
   We instrumented [Language] with [init_genv] and [init_gmem],
   such that the constraints over initialization of global envirionment and initial memories 
   could be abstract.
   We also instrumented [internal_fn] for finding the corresponding module from function id.
   - the runtime module [ModSem.t] is adapted from [linking.v] in Compositional CompCert.

   Other contents are newly developed.
*)

Require Import Setoid List Lists.Streams.
Require Import Coqlib Errors Values AST Globalenvs.
Require Import Footprint GMemory MemAux.


(** * Interaction Semantics *)

(** This file defines abstract module languages as interaction semantics. *)

(** An interaction semantics has these interfaces:
- [F], [V], [G]: 
types of function definition, variable information (e.g. Clight types), and global envirionment
- [comp_unit]: type of compilation unit
- [core]: type of internal "core" state
- [init_core]: initialize runtime core w.r.t. an entry and arguments, used on thread creation or external calls
- [halt]: core halts, a returning value is also required for supporting external calls
- [step]: internal steps of the core
- [at_external]: genrates events (EntAtom/ExtAtom/Print or an external callwith arguments) and yield control
The EnvAtom/ExtAtom/Print events are encoded as special external functions with fixed function idents defined in GAST.v
- [after_external]: get back control, a returning value is required for supporting external calls
- [internal_fn]: generate a function table (for generaing function-module mapping), we need an interface for internal function list 
- [init_genv], [init_gmem]: Because we do not instantiate a concrete initial state or symbol binding, we give language extensional checkings for proper initial genv and memory
    
 *)

Record Language :=
  { 
    F: Type;
    V: Type;
    G: Type;
    comp_unit: Type;

    core: Type;
    
    init_core: G -> ident -> list val -> option core;
    step: G -> freelist -> core -> gmem -> FP.t -> core -> gmem -> Prop;
    at_external: G -> core -> option (ident * signature * list val);
    after_external: core -> option val -> option core;
    halt: core -> option val;
    
    internal_fn: comp_unit -> list ident;
    init_genv: comp_unit -> Genv.t F V -> G -> Prop;
    init_gmem: Genv.t F V -> gmem -> Prop;
  }.

(** Type of sequential compiler. 
    The compiler is parameterized by the source and target languages *)
Definition seq_comp {sl tl: Language} : Type :=
  comp_unit sl -> res (comp_unit tl).


(** A [ModSemantics] is generated from a compilation unit.
    It provides the semantics of a module, 
    and is included in the global runtime environment.
 *)

Module ModSem.
  Record t :=
    {
      lang: Language;
      ge: Genv.t lang.(@F) lang.(@V);
      Ge: lang.(G);
    }.

  Inductive init_modsem (lang: Language) (cu: comp_unit lang) : t -> Prop :=
  | Init_modsem : forall ge Ge,
      init_genv lang cu ge Ge ->
      init_modsem lang cu (Build_t lang ge Ge).
  
End ModSem.

Inductive ge_wf {l: Language} (c: comp_unit l) (ge: Genv.t _ _) Ge : Prop :=
| Ge_wf: l.(@init_genv) c ge Ge -> ge_wf c ge Ge.

Inductive ModSem_wf {l: Language} : comp_unit l -> ModSem.t -> Prop :=
  ModSemWF : forall cu ge Ge,
    l.(init_genv) cu ge Ge->
    ModSem_wf cu (ModSem.Build_t l ge Ge).

Theorem ge_wf_ModSem_wf:
  forall l c ge Ge,
    @ge_wf l c ge Ge->
    ModSem_wf c (ModSem.Build_t l ge Ge).
Proof. intros. inversion H. constructor. auto. Qed.




(** * Language Properties *)

Definition abort (lang: Language) ge fl q m: Prop :=
  (forall fp q' m', ~ lang.(@step) ge fl q m fp q' m') /\
  (lang.(@at_external) ge q = None) /\
  (lang.(@halt) q = None).


Section LangProp.

  Context {F V G core : Type}.
  Variable init_gmem: Genv.t F V -> gmem -> Prop.
  Variable step : G -> freelist -> core -> gmem -> FP.t -> core -> gmem -> Prop.
  Variable at_external : G -> core -> option (ident * signature * list val).
  Variable halt : core -> option val.

  Definition init_gmem_valid': Prop :=
    forall ge gm, init_gmem ge gm ->
             forall b, Plt b (Genv.genv_next ge) -> GMem.valid_block gm b.
    
  Definition belongsto:=Locs.belongsto.
  Definition notbelongsto (l:Locs.t):= fun b ofs=> (l b ofs=false).
  Definition unchanged_validity (P:block->Z->Prop)(m m':GMem.gmem'):Prop:=
    forall b ofs,
      P b ofs ->
      GMem.valid_block m b <-> GMem.valid_block m' b.
  Definition unchanged_perm (P:block->Z->Prop)(m m':GMem.gmem'):Prop:=
    unchanged_validity P m m' /\ GMem.eq_perm P m m'.
  Definition unchanged_content (P:block->Z->Prop)(m m':GMem.gmem'):Prop:=
    unchanged_perm P m m' /\
    forall b ofs,P b ofs ->GMem.perm m b ofs Memperm.Max Memperm.Readable->
            Maps.ZMap.get ofs (Maps.PMap.get b m'.(GMem.mem_contents)) =
            Maps.ZMap.get ofs (Maps.PMap.get b m.(GMem.mem_contents)).

  Definition depends (fp: FP.t) : Locs.t :=
    Locs.union (FP.cmps fp) (FP.reads fp).

  Definition effects (fp: FP.t) : Locs.t :=
    Locs.union (FP.writes fp) (FP.frees fp).

  Inductive perm_effect (m m': gmem) (b: block) (ofs: Z) : Prop :=
  | Perm_effect_drop: forall k p,
      GMem.perm m b ofs k p ->
      ~ GMem.perm m' b ofs k p ->
      perm_effect m m' b ofs
  | Perm_effect_rise: forall k p,
      ~ GMem.perm m b ofs k p ->
      GMem.perm m' b ofs k p ->
      perm_effect m m' b ofs.

  (** This property characterizes that the extensional memory effect 
      between [m_before] and [m_after] is captured by footprint [fp],
      which means 
- [MemContentPreserve] : the memory contents stays unchanged outside [effects fp]
- [MemPermPreserve] : the memory permissions stay unchanged outside [frees fp]
- [PermEffect] : redundant field, could be implied from [MemPermPreserve], will be deleted in the future
- [ValidityPreserve] : the [validblocks] set could only be enlarged
   *)
  Record MemEffect (m_before m_after: gmem) (fp: FP.t): Prop :=
    {
      MemContentPreserve:
        unchanged_content (notbelongsto (effects fp)) m_before m_after;
      MemPermPreserve:
        unchanged_perm (notbelongsto fp.(FP.frees)) m_before m_after;
      PermEffect:
        forall b ofs, perm_effect m_before m_after b ofs -> Locs.belongsto (FP.frees fp) b ofs;
      ValidityPreserve:
        forall b, GMem.valid_block m_before b -> GMem.valid_block m_after b
    }.

  (** This property characterizes that allocation is performed locally in the freelist [fl] *)
  Definition LocalAlloc(m_before m_after: gmem) (fl: freelist): Prop :=
    forall b, ~GMem.valid_block m_before b -> GMem.valid_block m_after b -> in_fl fl b.

  (** This is the combinition of the above two properties, corresponds to LEffect in paper Fig. 6 *)
  Definition LEffect (m_before m_after: gmem) (fp: FP.t) (fl: freelist): Prop :=
    MemEffect m_before m_after fp /\ LocalAlloc m_before m_after  fl.

  (** This property characterizes the relation between two memory states such that 
      they are equivalent modulo [fp] 
- [ReadMemEq]: memory contents of location in [reads] are equal
- [CmpMemPermExists]: memory permissions of location in [cmps] are equal
- [EffectPermEqPre]: memory permissions of location in [writes] or [frees] are equal
   *)
  Record MemPre  (m_before m_before': gmem) (fp: FP.t) : Prop :=
    {
      ReadMemEq:
        unchanged_content (belongsto fp.(FP.reads)) m_before m_before';
      CmpMemPermExists:
        unchanged_perm (belongsto fp.(FP.cmps)) m_before m_before';
      EffectPermEqPre:
        forall b ofs, belongsto (effects fp) b ofs ->
                 (forall k p, GMem.perm m_before b ofs k p <-> GMem.perm m_before' b ofs k p);}.

  (** Block validities are equal modulo freelists *)
  Definition FreelistEq(m_before m_before': gmem)(fl: freelist) : Prop :=
    forall b, in_fl fl b ->
         GMem.valid_block m_before b <-> GMem.valid_block m_before' b.

  (** Combinition of properties above, corresponding to LPre in paper Fig.6 *)
  Definition LPre (m_before m_before': gmem) (fp: FP.t) (fl: freelist) : Prop :=
    MemPre m_before m_before' fp /\ FreelistEq m_before m_before' fl.

  (** Memory contents are equal modulo [writes] and [frees] *)
  Definition MemPost (m_after m_after': gmem) (fp: FP.t) : Prop :=
    unchanged_content (belongsto (effects fp) ) m_after m_after'.
  
  (** LPost in paper Fig. 6 *)
  Definition LPost (m_after m_after': gmem) (fp: FP.t) (fl: freelist) : Prop :=
    MemPost m_after m_after' fp /\ FreelistEq m_after m_after' fl.

  (** [validblocks] is enlarged after core step *)
  Definition corestep_forward :=
    forall ge fl q m fp q' m',
      step ge fl q m fp q' m' ->
      GMem.forward m m'.

  (** memory effect of core step is captured by its footprint *)
  Definition corestep_local_eff :=
    forall ge fl q m fp q' m',
      step ge fl q m fp q' m' ->
      LEffect m m' fp fl.

  (** if two memories are equal modulo the footprint and freelist of the core step,
      they are able to perform the same core step *)
  Definition corestep_locality_1:=
    forall ge fl q m fp q' m',
      step ge fl q m fp q' m' ->
      forall m0,
        LPre m m0 fp fl ->
        exists m0', step ge fl q m0 fp q' m0' /\
               LPost m' m0' fp fl.
  (** non-determinism of core-steps are captured by union of all possible [reads] and [cmps] *)
  Definition corestep_locality_2:=
    forall ge fl q m m0 fp0
      (H_step: exists fp1 q1 m1, step ge fl q m fp1 q1 m1),
      (* fp0 captures all possible footprint from state (q, m) *)
      (forall fp q' m', step ge fl q m fp q' m' -> FP.subset fp fp0) ->
      (* m0 and m are equal on fp0 *)
      LPre m m0 fp0 fl ->
      (* then any step from state (q, m0) could be performed on (q, m) *)
      (forall fp q' m0',
          step ge fl q m0 fp q' m0' ->
          exists m', step ge fl q m fp q' m').

  (** [step], [at_external] and [halt] are mutual-exclusive *)
  Definition corestep_not_at_external :=
    forall ge fl m q fp m' q',
      step ge fl q m fp q' m' -> at_external ge q = None.
  
  Definition corestep_not_halted :=
    forall ge fl m q fp m' q', step ge fl q m fp q' m' -> halt q = None.
  
  Definition at_external_halted_excl :=
    forall ge q, at_external ge q = None \/ halt q = None.

  (** Deterministic of step *)
  Definition step_det :=
    forall ge fl m q fp1 m1 q1 fp2 m2 q2,
      step ge fl q m fp1 q1 m1 ->
      step ge fl q m fp2 q2 m2 ->
      fp1 = fp2 /\
      q1 = q2 /\
      m1 = m2.

  Definition eq_mem_eq_corestep :=
    forall m1 m2,
      GMem.eq' m1 m2 ->
      (forall ge fl q fp m1' q',
          step ge fl q m1 fp q' m1' ->
          exists m2',
            step ge fl q m2 fp q' m2' /\
            GMem.eq' m1' m2').
  
  Lemma unchanged_validity_refl:
    forall P m,unchanged_validity P m m.
  Proof. split;intro;auto. Qed.
  Lemma unchanged_validity_comm:
    forall P m m',unchanged_validity P m m'->unchanged_validity P m' m.
  Proof. unfold unchanged_validity;intros;specialize (H b ofs H0) as [];split;auto. Qed.
  Lemma unchanged_validity_trans:
    forall P m1 m2 m3,unchanged_validity P m1 m2->unchanged_validity P m2 m3->
                 unchanged_validity P m1 m3.
  Proof. unfold unchanged_validity in *;intros;specialize (H b ofs H1);specialize (H0 b ofs H1);split;intro;[apply H0;apply H|apply H;apply H0];auto. Qed.
  Lemma unchanged_validity_implies:
    forall (P P':block->Z->Prop) m m',
      (forall b ofs, P b ofs -> P' b ofs) ->
      unchanged_validity P' m m'->
      unchanged_validity P m m'.
  Proof. unfold unchanged_validity;intros;specialize (H b ofs H1);specialize (H0 b ofs H);auto. Qed.
  Lemma unchanged_validity_union:
    forall P P' m m',
      unchanged_validity P m m'->unchanged_validity P' m m'->
      unchanged_validity (fun b ofs=>P b ofs \/ P' b ofs) m m'.
  Proof.
    unfold unchanged_validity;intros.
    destruct H1;[eapply H|eapply H0];eauto.
  Qed.
  Lemma unchanged_validity_union2:
    forall l1 l2 m m',
      unchanged_validity (belongsto l1) m m' ->
      unchanged_validity (belongsto l2) m m' ->
      unchanged_validity (belongsto(Locs.union l1 l2)) m m'.
  Proof.
    unfold unchanged_validity;intros.
    unfold belongsto in H1. Locs.unfolds.
    destruct l1 eqn:?;eauto.
  Qed.
  
  Lemma unchanged_perm_refl:
    forall P m,unchanged_perm P m m.
  Proof. intros;constructor. apply unchanged_validity_refl. intros;split;auto. Qed.
  Lemma unchanged_perm_comm:
    forall P m m',unchanged_perm P m m'->unchanged_perm P m' m.
  Proof. unfold unchanged_perm;intros. destruct H. split;[apply unchanged_validity_comm|unfold GMem.eq_perm;intros];auto;specialize (H0 b ofs k p H1) as [];split;auto. Qed.
  Lemma unchanged_perm_trans:
    forall P m m1 m2,unchanged_perm P m m1 ->unchanged_perm P m1 m2->unchanged_perm P m m2.
  Proof. unfold unchanged_perm;intros P m m1 m2 [] [];split;[eapply unchanged_validity_trans|];eauto. unfold GMem.eq_perm;intros; specialize (H0 b ofs k p H3) as [];specialize (H2 b ofs k p H3) as [];split;auto. Qed.
  Lemma unchanged_perm_implies:
    forall (P P':block->Z->Prop),
      (forall b ofs,P' b ofs->P b ofs)->
      forall m m', unchanged_perm P m m' ->unchanged_perm P' m m'.
  Proof.
    unfold unchanged_perm;intros P P' H m m' [];split.
    eapply unchanged_validity_implies;eauto.
    unfold GMem.eq_perm;intros;specialize (H1 b ofs k p (H b ofs H2)) as [];split;auto.
  Qed.
  Lemma unchanged_perm_union:
    forall P P' m m',
      unchanged_perm P m m' -> unchanged_perm P' m m' -> unchanged_perm (fun b ofs=>P b ofs \/ P' b ofs) m m'.
  Proof.
    unfold unchanged_perm;intros P P' m m' [] [];split.
    apply unchanged_validity_union;auto.
    intros b ofs k p [];[apply H0|apply H2];auto.
  Qed.
  Lemma unchanged_perm_union2:
    forall l1 l2 m m',
      unchanged_perm (belongsto l1)m m' ->
      unchanged_perm (belongsto l2)m m' ->
      unchanged_perm (belongsto(Locs.union l1 l2)) m m'.
  Proof. unfold unchanged_perm;intros. destruct H,H0;split. apply unchanged_validity_union2;auto. unfold GMem.eq_perm;intros. unfold belongsto in H3. unfold Locs.belongsto in H3. unfold Locs.union in H3. destruct l1 eqn:?;eauto. Qed.
  
  Lemma unchanged_content_refl:
    forall P m,unchanged_content P m m.
  Proof. intros;split;[apply unchanged_perm_refl|intros];auto. Qed.
  Lemma unchanged_content_comm:
    forall P m m',unchanged_content P m m'->unchanged_content P m' m.
  Proof. unfold unchanged_content;intros P m m' [];split;[apply unchanged_perm_comm|intros;symmetry;apply H0];auto. destruct H;apply H3;auto. Qed.
  Lemma unchanged_content_trans:
    forall P m m1 m2,unchanged_content P m m1 -> unchanged_content P m1 m2-> unchanged_content P m m2.
  Proof. unfold unchanged_content;intros P m m1 m2 [] [];split;[eapply unchanged_perm_trans|intros;rewrite H2];eauto. destruct H;apply H5;auto. Qed.
  Lemma unchanged_content_implies:
    forall (P P':block->Z->Prop),
      (forall b ofs,P' b ofs ->P b ofs)->
      forall m m',unchanged_content P m m'->unchanged_content P' m m'.
  Proof. unfold unchanged_content;intros P P' H m m' [];split;[eapply unchanged_perm_implies|];eauto. Qed.
  Lemma unchanged_content_union:
    forall P P' m m',
      unchanged_content P m m'->unchanged_content P' m m'->
      unchanged_content (fun b ofs=> P b ofs \/ P' b ofs) m m'.
  Proof. unfold unchanged_content;intros P P' m m' [] [];split;[apply unchanged_perm_union|intros b ofs []];auto. Qed.
  Lemma unchanged_content_union2:
    forall l1 l2 m m',
      unchanged_content (belongsto l1)m m'->
      unchanged_content (belongsto l2)m m'->
      unchanged_content (belongsto (Locs.union l1 l2)) m m'.
  Proof. unfold unchanged_content;intros. destruct H,H0;split;auto. apply unchanged_perm_union2;auto. intros. unfold belongsto in H3;unfold Locs.union in H3;unfold Locs.belongsto in H3;destruct l1 eqn:?;eauto. Qed.
  Lemma Memperm_validblock:
    forall m b ofs k p,
      GMemory.GMem.perm m b ofs k p ->
      GMemory.GMem.valid_block m b.
  Proof.
    destruct m.
    intros.
    unfold GMemory.GMem.valid_block.
    simpl .
    unfold GMemory.GMem.perm in H;simpl in H.
    apply Classical_Prop.NNPP;intro.
    eapply invalid_noaccess in H0;eauto.
    rewrite H0 in H.
    inversion H.
  Qed.
  Lemma perm''_cur_max:
    forall m b ofs,
      Memperm.perm_order'' (Maps.PMap.get b (GMem.mem_access m) ofs Memperm.Max)(Maps.PMap.get b (GMem.mem_access m) ofs Memperm.Cur).
  Proof. destruct m;eauto. Qed.
  Lemma perm_order'_'':
    forall m b ofs p,
      Memperm.perm_order' (Maps.PMap.get b (GMem.mem_access m) ofs Memperm.Cur) p->
      Memperm.perm_order' (Maps.PMap.get b (GMem.mem_access m) ofs Memperm.Max) p.
  Proof.
    unfold Memperm.perm_order'.
    intros.
    pose proof perm''_cur_max m b ofs.
    unfold Memperm.perm_order'' in H0.
    destruct ( Maps.PMap.get b (GMem.mem_access m) ofs Memperm.Cur);
      destruct ( Maps.PMap.get b (GMem.mem_access m) ofs Memperm.Max);
      try contradiction.
    eapply Memperm.perm_order_trans;eauto.
  Qed.
  Ltac unfolds :=
    unfold unchanged_content;unfold unchanged_perm;unfold unchanged_validity.

  Lemma unchanged_content_equiv:
    forall P m m',
      unchanged_content P m m' -> GMem.unchanged_on P m m'.
  Proof.
    intros.
    destruct H as [[] ].
    constructor;auto.
  Qed.


  
  Lemma depends_union:
    forall fp1 fp2,depends (FP.union fp1 fp2)=Locs.union (depends fp1)(depends fp2).
  Proof.
    destruct fp1,fp2; unfold depends;unfold FP.union;unfold Locs.union;simpl;intros.
    apply FunctionalExtensionality.functional_extensionality;intro.
    apply FunctionalExtensionality.functional_extensionality;intro.
    destruct cmps,cmps0,reads,reads0;auto.
  Qed.
  Lemma effects_union:
    forall fp1 fp2,effects (FP.union fp1 fp2) = Locs.union (effects fp1)(effects fp2).
  Proof.
    destruct fp1,fp2; unfold effects;unfold FP.union;unfold Locs.union;simpl;intros.
    apply FunctionalExtensionality.functional_extensionality;intro.
    apply FunctionalExtensionality.functional_extensionality;intro.
    destruct writes,writes0,frees,frees0;auto.
  Qed.
  
  Lemma perm_effect_comm:
    forall m m' b ofs,perm_effect m m' b ofs ->perm_effect m' m b ofs.
  Proof. intros;inversion H;[econstructor 2|econstructor];eauto. Qed.
  Lemma perm_effect_insert:
    forall m m' b ofs,
      perm_effect m m' b ofs->
      forall m'',perm_effect m m'' b ofs \/ perm_effect m' m'' b ofs.
  Proof. intros.
         inversion H. assert(GMem.perm m'' b ofs k p\/ ~GMem.perm m'' b ofs k p);[apply Classical_Prop.classic|];destruct H2;[right;econstructor 2|left;econstructor];eauto.
         assert(GMem.perm m'' b ofs k p\/ ~GMem.perm m'' b ofs k p);[apply Classical_Prop.classic|];destruct H2;[left;econstructor 2|right;econstructor];eauto.
  Qed.
  
  
  Lemma contra_belongsto:
    forall l b ofs, ~ belongsto l b ofs <-> notbelongsto l b ofs.
  Proof. unfold belongsto;unfold Locs.belongsto;unfold notbelongsto;intros;destruct (l b ofs);split;intro;auto;try contradiction;inversion H. Qed.
  Lemma belongsto_union:
    forall l1 l2 b ofs,
      Locs.belongsto (Locs.union l1 l2) b ofs <->
      Locs.belongsto l1 b ofs \/ Locs.belongsto l2 b ofs.
  Proof. unfold Locs.belongsto;unfold Locs.union;intros;destruct (l1 b ofs),(l2 b ofs);split;intro;auto. inversion H;auto. Qed.
  Lemma belongsto_subset:
    forall l1 l2,
      Locs.subset l2 l1->
      forall b ofs,
        belongsto l2 b ofs->
        belongsto l1 b ofs.
  Proof. intros. unfold Locs.subset in H. apply H. assumption. Qed.
  Lemma notbelongsto_union:
    forall l1 l2 b ofs,
      notbelongsto (Locs.union l1 l2) b ofs <->
      notbelongsto l1 b ofs /\ notbelongsto l2 b ofs.
  Proof. split;unfold notbelongsto;unfold Locs.union;intros;destruct (l1 b ofs),(l2 b ofs);auto;inversion H;auto. Qed.
  Lemma notbelongsto_subset:
    forall l1 l2,
      Locs.subset l1 l2->
      forall b ofs,
        notbelongsto l2 b ofs->
        notbelongsto l1 b ofs.
  Proof. intros. unfold notbelongsto in *. unfold Locs.subset in H. unfold Locs.belongsto in H. destruct (l1 b ofs) eqn:eq. apply H in eq. rewrite eq in H0. auto. auto.
  Qed.

  Lemma belongsto_or_notbelongsto:
    forall l b ofs,belongsto l b ofs \/ notbelongsto l b ofs.
  Proof. intros. unfold belongsto;unfold Locs.belongsto;unfold notbelongsto. destruct l;auto. Qed.
  

  Lemma perm_order'_equiv:
    forall p1 p2,
      (forall p,Memperm.perm_order' p1 p <-> Memperm.perm_order' p2 p) ->
      p1 = p2.
  Proof.
    intros.
    unfold Memperm.perm_order' in H.
    destruct p1,p2;auto.
    specialize (H p) as L1.
    specialize (H p0) as [].
    destruct L1.
    specialize (H1 (Memperm.perm_refl p)).
    specialize (H0 (Memperm.perm_refl p0)).
    clear H H2.
    f_equal.
    destruct p,p0;inversion H1;inversion H0;subst;auto.
    
    destruct (H p).
    contradict H0. constructor.
    destruct (H p).
    contradict H1. constructor.
  Qed.

  Lemma unchanged_content_memeq:
    forall m m' l,
      unchanged_content (belongsto l) m m'->
      unchanged_content (notbelongsto l)m m'->
      GMem.eq' m m'.
  Proof.
    intros.
    destruct H as [[] ],H0 as [[] ].
    unfold unchanged_validity in *.

    constructor;intros.
    (*apply perm_order'_'' in H5.*)
    pose proof belongsto_or_notbelongsto l b ofs as [];symmetry;eauto.
    assert(forall p, GMem.perm m b ofs k p <->GMem.perm m' b ofs k p).
    pose proof belongsto_or_notbelongsto l b ofs as [];intro;eauto.
    apply GMem.eq_access_eq_perm.
    unfold GMem.perm in H5.
    
    apply perm_order'_equiv;auto.
    pose proof belongsto_or_notbelongsto l b 0 as [];eauto.
  Qed.

  Lemma unchanged_validity_emp:
    forall m1 m2,unchanged_validity (belongsto Locs.emp) m1 m2.
  Proof.
    unfold unchanged_validity;intros;inversion H.
  Qed.
  
  Lemma unchanged_perm_emp:
    forall m1 m2,unchanged_perm (belongsto Locs.emp) m1 m2 .
  Proof.
    unfold unchanged_perm;intros;split. eapply unchanged_validity_emp.
    unfold GMem.eq_perm;intros. inversion H.
  Qed.
  
  Lemma unchanged_content_emp:
    forall m1 m2,unchanged_content (belongsto Locs.emp) m1 m2.
  Proof.
    unfold unchanged_content;intros;split. apply unchanged_perm_emp.
    intros. inversion H.
  Qed.
  
  
  Lemma MemEffect_refl:
    forall m fp,MemEffect m m fp.
  Proof.
    intros;split. apply unchanged_content_refl. apply unchanged_perm_refl.
    intros. inversion H;contradiction.
    eauto.
  Qed.
  
  Lemma LocalAlloc_refl:
    forall m fl,LocalAlloc m m fl.
  Proof.  unfold LocalAlloc;intros;contradiction. Qed.
  
  Corollary LEffect_refl:
    forall m fp fl,LEffect m m fp fl.
  Proof. split;[apply MemEffect_refl|apply LocalAlloc_refl]. Qed.
  
  Lemma MemEffect_trans:
    forall m1 m2 m3 fp,
      MemEffect m1 m2 fp ->
      MemEffect m2 m3 fp ->
      MemEffect m1 m3 fp.
  Proof.
    intros m1 m2 m3 fp [] [].
    constructor;auto.
    eapply unchanged_content_trans;eauto.
    eapply unchanged_perm_trans;eauto.
    intros.
    eapply perm_effect_insert in H as [];[|eapply perm_effect_comm in H];eauto.
  Qed.
  
  Lemma LocalAlloc_trans:
    forall m1 m2 m3 fl,
      LocalAlloc m1 m2 fl->
      LocalAlloc m2 m3 fl->
      LocalAlloc m1 m3 fl.
  Proof.
    unfold LocalAlloc;intros.
    assert(GMem.valid_block m2 b \/ ~ GMem.valid_block m2 b).
    apply Classical_Prop.classic.
    destruct H3;eauto.
  Qed.
  
  Corollary LEffect_trans:
    forall m1 m2 m3 fp fl,
      LEffect m1 m2 fp fl->
      LEffect m2 m3 fp fl->
      LEffect m1 m3 fp fl.
  Proof.
    unfold LEffect;intros m1 m2 m3 fp fl [] [].
    split;[eapply MemEffect_trans|eapply LocalAlloc_trans];eauto.
  Qed.
  
  Lemma MemEffect_union_fp:
    forall m m' fp1 fp2,
      MemEffect m m' fp1->
      MemEffect m m' (FP.union fp1 fp2).
  Proof.
    intros m m' fp1 fp2 [].
    constructor;auto.
    eapply unchanged_content_implies;try apply MemContentPreserve0.
    intros. rewrite effects_union in H. apply notbelongsto_union in H as [];auto.
    eapply unchanged_perm_implies;try apply PermEffect0.
    intros. assert(FP.frees(FP.union fp1 fp2)=Locs.union(FP.frees fp1)(FP.frees fp2)). unfold FP.frees;unfold FP.union;auto.
    rewrite H0 in H. apply notbelongsto_union in H as []. eapply H. auto.
    intros. apply PermEffect0 in H. apply belongsto_union. auto.
  Qed.
  
  Corollary LEffect_union_fp: forall m m' fp1 fp2 fl,LEffect m m' fp1 fl->LEffect m m' (FP.union fp1 fp2) fl.
  Proof.
    unfold LEffect;intros m m' fp1 fp2 fl [];constructor;auto;eapply MemEffect_union_fp;eauto.
  Qed.
  
  Corollary LEffect_trans_union:
    forall m1 m2 m3 fp1 fp2 fl,
      LEffect m1 m2 fp1 fl->LEffect m2 m3 fp2 fl->LEffect m1 m3(FP.union fp1 fp2)fl.
  Proof. intros;eapply LEffect_trans;[|rewrite FP.union_comm_eq];eapply LEffect_union_fp;eauto. Qed.
  
  Lemma MemPre_refl:
    forall m fp,MemPre m m fp.
  Proof. intros;constructor. apply unchanged_content_refl. apply unchanged_perm_refl. split;auto. Qed.
  
  Lemma FreelistEq_refl: forall m fl,FreelistEq m m fl.
  Proof. constructor;intro;auto. Qed.
  
  Lemma LPre_refl: forall m fp fl,LPre m m fp fl.
  Proof. intros. constructor. apply MemPre_refl. apply FreelistEq_refl. Qed.
  
  Lemma MemPre_comm:
    forall m m' fp,
      MemPre m m' fp -> MemPre m' m fp.
  Proof.
    intros m m' fp [];constructor;auto.
    apply unchanged_content_comm;auto.
    apply unchanged_perm_comm;auto.
    split;eapply EffectPermEqPre0;eauto.
  Qed.
  
  Lemma FreelistEq_comm:
    forall m m' fl,
      FreelistEq m m' fl -> FreelistEq m' m fl.
  Proof. unfold FreelistEq;intros;split;intro;eapply H;eauto. Qed.
  
  Lemma LPre_comm: forall m m' fp fl,LPre m m' fp fl->LPre m' m fp fl.
  Proof. constructor;destruct H;[apply MemPre_comm|apply FreelistEq_comm];auto. Qed.
  
  Lemma MemPre_trans:
    forall m1 m2 m3 fp,
      MemPre m1 m2 fp->
      MemPre m2 m3 fp->
      MemPre m1 m3 fp.
  Proof.
    intros.
    destruct H,H0.
    constructor;auto.
    eapply unchanged_content_trans;eauto.
    eapply unchanged_perm_trans;eauto.
    split;intros; edestruct EffectPermEqPre0, EffectPermEqPre1;eauto.
    Unshelve. auto. auto. auto. auto.
  Qed.
  
  Lemma FreelistEq_trans:
    forall m1 m2 m3 fl,
      FreelistEq m1 m2 fl->
      FreelistEq m2 m3 fl->
      FreelistEq m1 m3 fl.
  Proof.
    unfold FreelistEq in *;split;intros;edestruct H,H0;eauto.
  Qed.
  
  Lemma LPre_trans: forall m1 m2 m3 fp fl,LPre m1 m2 fp fl->LPre m2 m3 fp fl->LPre m1 m3 fp fl.
  Proof. unfold LPre;intros ? ? ? ? ? [] [];constructor;[eapply MemPre_trans|eapply FreelistEq_trans];eauto. Qed.
  
  Lemma Locs_union_subset2:
    forall l1 l2 l3 l4,
      Locs.subset l1 l3->
      Locs.subset l2 l4->
      Locs.subset (Locs.union l1 l2)(Locs.union l3 l4).
  Proof. Locs.unfolds. intros. destruct (l1 b ofs) eqn:eq1,(l2 b ofs) eqn:eq2;try apply H in eq1;try apply H0 in eq2;try rewrite eq1;try rewrite eq2;auto. destruct (l3 b ofs);auto. inversion H1. Qed.
  
  Lemma MemPre_subset:
    forall fp fp',
      FP.subset fp fp'->
      forall m m' ,
        MemPre m m' fp' ->
        MemPre m m' fp .
  Proof.
    intros fp fp' [] m m'  [].
    constructor.
    eapply unchanged_content_implies. apply belongsto_subset. eauto. eauto.
    eapply unchanged_perm_implies. apply belongsto_subset. eauto. eauto.
    intros. unfold effects in *. edestruct EffectPermEqPre0. eapply belongsto_subset. eapply Locs_union_subset2;eauto. eauto. split;auto.
  Qed.
  
  Corollary LPre_subset:
    forall fp fp',
      FP.subset fp fp'->
      forall m m' fl,
        LPre m m' fp' fl ->
        LPre m m' fp fl.
  Proof.
    unfold LPre;intros.
    destruct H0;split;auto.
    eapply MemPre_subset;eauto.
  Qed.
    
  Lemma LPost_refl: forall m fp fl,LPost m m fp fl.
  Proof. intros;constructor;[apply unchanged_content_refl|split;intro];auto. Qed.
  
  Lemma LPost_comm: forall m m' fp fl,LPost m m' fp fl->LPost m' m fp fl.
  Proof. destruct 1;split. apply unchanged_content_comm;auto. apply FreelistEq_comm;auto. Qed.

  Lemma LPost_trans: forall m1 m2 m3 fp fl,LPost m1 m2 fp fl->LPost m2 m3 fp fl->LPost m1 m3 fp fl.
  Proof. intros m1 m2 m3 fp fl [] [];constructor;[eapply unchanged_content_trans|eapply FreelistEq_trans];eauto. Qed.
  
  Lemma LPost_subset:
    forall fp fp',
      FP.subset fp fp'->
      forall m m' fl,
        LPost m m' fp' fl->
        LPost m m' fp fl.
  Proof. intros fp fp' [] m m' fl [];constructor;auto;eapply unchanged_content_implies. eapply belongsto_subset. unfold effects. eapply Locs_union_subset2;eauto. auto. Qed.
  
  Lemma MemPre_MemEffect_MemPost_Rule:
    forall m0 m1 m0' m1' fp1 fp2,
      MemPre m0 m0' (FP.union fp1 fp2)->
      MemEffect m0 m1 fp1 ->
      MemEffect m0' m1' fp1->
      MemPost m1 m1' fp1 ->
      MemPre m1 m1' fp2.
  Proof.
    intros until fp2.
    intros [] [] [] EffectMemEqPost0.
    unfold MemPost in EffectMemEqPost0.
    assert(L1:unchanged_validity (belongsto (FP.reads fp2)) m1 m1').
    unfolds;intros. assert(belongsto (effects fp1) b ofs\/ ~belongsto (effects fp1) b ofs). apply Classical_Prop.classic. destruct H0. edestruct EffectMemEqPost0 as [[[] ] ];eauto. split;auto.
    apply contra_belongsto in H0.
    edestruct MemContentPreserve0 as [[[] ] ],MemContentPreserve1 as [[[] ] ];eauto.
    clear H3 H4 H7.
    apply belongsto_subset with(l1:=(FP.reads(FP.union fp1 fp2))) in H.
    edestruct ReadMemEq0 as [[[] _] _];eauto.
    split;intro;auto.
    unfold FP.union;Locs.unfolds;simpl;intros;destruct (FP.reads fp1 b0 ofs0);auto.

    assert(L2:unchanged_validity (belongsto (FP.cmps fp2)) m1 m1').
    unfolds;intros. assert(belongsto (effects fp1) b ofs\/ ~belongsto (effects fp1) b ofs). apply Classical_Prop.classic. destruct H0. edestruct EffectMemEqPost0 as [[[] ] ];eauto. split;auto.
    apply contra_belongsto in H0.
    edestruct MemContentPreserve0 as [[[] ] ],MemContentPreserve1 as [[[] ] ];eauto. 
    clear H3 H4 H7.
    apply belongsto_subset with(l1:=(FP.cmps(FP.union fp1 fp2))) in H.
    edestruct CmpMemPermExists0 as [[] _];eauto.
    split;intro;auto.
    unfold FP.union;Locs.unfolds;simpl;intros;destruct (FP.cmps fp1 b0 ofs0);auto.

    assert(L1':unchanged_perm (belongsto (FP.reads fp2)) m1 m1').
    split;auto;unfold GMem.eq_perm;intros.
    assert(belongsto (effects fp1) b ofs\/ ~belongsto (effects fp1) b ofs). apply Classical_Prop.classic. destruct H0. edestruct EffectMemEqPost0 as [[[] ] ];eauto.
    apply contra_belongsto in H0.
    edestruct MemContentPreserve0 as [[_ []]_],MemContentPreserve1 as [[_ []]_];eauto.
    apply belongsto_subset with(l1:=(FP.reads(FP.union fp1 fp2))) in H.
    edestruct ReadMemEq0 as [[_ []] _];eauto.
    split;intro;eauto.
    unfold FP.union;Locs.unfolds;simpl;intros;destruct (FP.reads fp1 b0 ofs0);auto.

    assert(L2':unchanged_perm (belongsto (FP.cmps fp2)) m1 m1').
    split;auto;unfold GMem.eq_perm;intros.
    assert(belongsto (effects fp1) b ofs\/ ~belongsto (effects fp1) b ofs). apply Classical_Prop.classic. destruct H0. edestruct EffectMemEqPost0 as [[[] ] ];eauto.
    apply contra_belongsto in H0.
    
    apply belongsto_subset with(l1:=(FP.cmps(FP.union fp1 fp2))) in H.
    edestruct CmpMemPermExists0 as [_ []];eauto.
    edestruct MemContentPreserve0 as [[_ []]_],MemContentPreserve1 as [[_ []]_];eauto.
    split;intro;eauto.
    unfold FP.union;Locs.unfolds;simpl;intros;destruct (FP.cmps fp1 b0 ofs0);auto.

    assert(L1'':unchanged_content (belongsto (FP.reads fp2)) m1 m1').
    split;auto;intros b ofs T1 T2.
    assert(belongsto (effects fp1) b ofs\/ ~belongsto (effects fp1) b ofs). apply Classical_Prop.classic. destruct H. edestruct EffectMemEqPost0 as [_ [] ];eauto.
    apply contra_belongsto in H.
    destruct MemContentPreserve0,MemContentPreserve1.
    edestruct H0 as [_ [_]];eauto.
    specialize (H4 T2).
    destruct ReadMemEq0 as [[_ ] ].
    edestruct H5 as [? _];eauto.
    apply belongsto_union;eauto.
    specialize (H7 H4).
    edestruct H2 as [_[? _]];eauto.
    specialize (H8 H7).
    rewrite H3;auto.
    rewrite H1;auto.
    rewrite H6;auto.
    apply belongsto_union;eauto.

    constructor;auto.
    
    intros.
    assert(belongsto (effects fp1) b ofs \/ ~ belongsto (effects fp1) b ofs). apply Classical_Prop.classic. destruct H0.
    edestruct EffectMemEqPost0 as [[_[]] _];eauto;split;eauto.
    apply contra_belongsto in H0.
    edestruct EffectPermEqPre0. rewrite effects_union. apply belongsto_union;eauto.
    edestruct MemContentPreserve0 as [[_[]] _],MemContentPreserve1 as [[_[]]_];eauto.
    split;intro;eauto.

    Unshelve. auto. auto. auto. auto. auto. auto.
  Qed.
  
  Lemma LPre_LEffect_LPost_Rule:
    forall m0 m1 m0' m1' fp1 fp2 fl1 fl2 fl3 fl4,
      LPre m0 m0' (FP.union fp1 fp2) fl1->
      LEffect m0 m1 fp1 fl2 ->
      LEffect m0' m1' fp1 fl3->
      LPost m1 m1' fp1 fl4 ->
      LPre m1 m1' fp2 fl4.
  Proof.
    intros m0 m1 m0' m1' fp1 fp2 fl1 fl2 fl3 fl4 [] [] [] [].
    constructor;auto.
    eapply MemPre_MemEffect_MemPost_Rule;eauto.
  Qed.
  
  Lemma MemPost_MemEffect_MemPost_Rule:
    forall m0 m1 m0' m1' fp1 fp2,
      MemPost m0 m1 fp1 ->
      MemEffect m0 m0' fp2 ->
      MemEffect m1 m1' fp2 ->
      MemPost m0' m1' fp2 ->
      MemPost m0' m1' (FP.union fp1 fp2).
  Proof.
    intros.
    destruct H1,H0.
    unfold MemPost in *.
    rename H into EffectMemEqPost0.
    rename H2 into EffectMemEqPost1.
    rewrite effects_union.
    eapply unchanged_content_implies.
    instantiate (1:= (fun b ofs=>belongsto (effects fp2) b ofs \/ (notbelongsto (effects fp2) b ofs /\ belongsto (effects fp1) b ofs))).
    simpl;intros.
    unfold belongsto in *;unfold notbelongsto;Locs.unfolds.
    destruct (effects fp2 b ofs) eqn:?;destruct (effects fp1 b ofs) eqn:?;Coqlib.inv H;auto.
    eapply unchanged_content_union;eauto.
    remember  (fun b ofs=> (notbelongsto (effects fp2) b ofs /\ belongsto (effects fp1) b ofs)) as P.
    assert(forall b ofs,P b ofs -> belongsto (effects fp1) b ofs).
    intros. rewrite HeqP in H. destruct H;auto.
    assert(forall b ofs,P b ofs -> notbelongsto (effects fp2) b ofs).
    intros. rewrite HeqP in H0. destruct H0;auto.
    eapply unchanged_content_implies in EffectMemEqPost0;eauto.
    eapply unchanged_content_implies in MemContentPreserve0;eauto.
    eapply unchanged_content_implies in MemContentPreserve1;eauto.
    eapply unchanged_content_trans;eauto.
    eapply unchanged_content_trans;eauto.
    eapply unchanged_content_comm;eauto.
  Qed.
     
  Lemma LPost_LEffect_LPost_Rule:
    forall m0 m1 m0' m1' fp1 fp2 fl1 fl2 fl3 fl4,
      LPost m0 m1 fp1 fl1->
      LEffect m0 m0' fp2 fl2->
      LEffect m1 m1' fp2 fl3->
      LPost m0' m1' fp2 fl4->
      LPost m0' m1' (FP.union fp1 fp2) fl4.  
  Proof.
    intros.
    destruct H,H0,H1,H2.
    constructor;auto.
    eapply MemPost_MemEffect_MemPost_Rule;eauto.
  Qed.
    
  Lemma Loc_smile_comm:
    forall l1 l2,
      Locs.smile l1 l2->Locs.smile l2 l1.
  Proof. Locs.unfolds. intros. specialize (H b ofs). destruct (l1 b ofs),(l2 b ofs);auto. Qed.
  
  Lemma LocSmile_belongsto_relation:
    forall l1 l2,
      Locs.smile l1 l2 ->
      forall b ofs, belongsto l1 b ofs->notbelongsto l2 b ofs.
  Proof.
    intros.
    unfold belongsto in H0. unfold notbelongsto.
    Locs.unfolds.
    destruct (l1 b ofs) eqn:e1,(l2 b ofs) eqn:e2;auto.
    specialize (H b ofs). rewrite e1 in H;rewrite e2 in H. inversion H.
  Qed.
  
  Ltac unfoldands:=
    repeat match goal with [H:_/\_|-_]=> destruct H end.

  Lemma MemEffect_fpsmile_MemPre_Rule:
    forall  m0 m1 fp1 fp2,
      MemEffect m0 m1 fp1 ->
      FP.smile fp1 fp2->
      MemPre m1 m0 fp2.
  Proof.
    intros.
    destruct H,H0.
    unfoldands.
    repeat match goal with [H: Locs.smile ?a ?b |- _ ]=> pose proof LocSmile_belongsto_relation a b H;pose proof LocSmile_belongsto_relation b a (Loc_smile_comm a b H);clear H end.
    split.
    eapply unchanged_content_implies.
    intros. assert( notbelongsto (effects fp1) b ofs).
    intros; apply notbelongsto_union;auto.
    apply H20. apply unchanged_content_comm. auto.
    eapply unchanged_perm_implies;eauto. apply unchanged_perm_comm;auto.
    intros.
    assert (notbelongsto (effects fp1) b ofs).
    unfold effects in *;intros.
    apply belongsto_union in H5 as [];apply notbelongsto_union;split;[apply H10|apply H11|apply H13|apply H8];auto.
    edestruct MemContentPreserve0 as [[_[]] _];eauto;split;auto.
  Qed.
    
  Lemma disjoint_fl_memeq:
    forall m0 m1 fl1 fl2,
      disj fl1 fl2 ->
      LocalAlloc m0 m1 fl1 ->
      (forall b, GMem.valid_block m0 b -> GMem.valid_block m1 b)->
      FreelistEq m0 m1 fl2.
  Proof.
    intros. apply FreelistEq_comm.
    unfold FreelistEq;intros.
    assert (~in_fl fl1 b).
    unfold in_fl in *.
    destruct H2. intro. destruct H3.
    inversion H. 
    rewrite <- H2 in H3.
    edestruct H4;eauto.
    
    split;intro.
    apply Classical_Prop.NNPP;intro.
    edestruct H0;eauto.
    apply H1;auto.
  Qed.
  
  Lemma LEffect_fpsmile_LPre_Rule:
    forall m0 m1 fp1 fp2 fl1 fl2,
      disj fl1 fl2 ->
      LEffect m0 m1 fp1 fl1 ->
      FP.smile fp1 fp2->
      LPre m1 m0 fp2 fl2.
  Proof.
    intros.
    destruct H0.
    constructor.
    eapply MemEffect_fpsmile_MemPre_Rule;eauto.
    destruct H0.
    eapply FreelistEq_comm.
    eapply disjoint_fl_memeq;eauto.
  Qed.
    
 
  Lemma LEffect_unchanged_on:
    forall fl m fp m',
      LEffect m m' fp fl ->
      GMem.unchanged_on (fun b ofs => ~ Locs.belongsto (FP.locs fp) b ofs) m m'.
  Proof.
    destruct 1 as [? _].
    destruct H as [? _ _ _].
    apply unchanged_content_equiv.
    eapply unchanged_content_implies;eauto.
    unfold Locs.belongsto;unfold notbelongsto.
    intros. unfold effects. unfold FP.locs in H.
    unfold Locs.union in *.
    destruct fp;simpl in *.
    destruct cmps,reads,frees,writes;eauto;try contradiction.
  Qed.

  Lemma LEffect_local_alloc:
    forall fl m fp m',
      LEffect m m' fp fl ->
      (forall b, GMem.valid_block m' b ->
                 ~ GMem.valid_block m b ->
                 in_fl fl b).
  Proof.
    inversion 1; auto.
  Qed.
  
End LangProp.

(** The well-defined language (Def. 1) in paper 
- [mem_enlarge]: Def.1 (1) 
- [mem_unchg_outside_writes]: Def.1 (2) 
- [step_sim_pre_post]: Def.1 (3) 
- [step_nondet_equiv]: Def.1 (4) 
 *)
Record wdFP (L: Language): Prop :=
  {
    mem_enlarge: corestep_forward (step L);
    mem_unchg_outside_writes: corestep_local_eff (step L);
    step_sim_pre_post: corestep_locality_1 (step L);
    step_nondet_equiv: corestep_locality_2 (step L);
  }.

(** For the convenience of proof development, we wrapped the [wdFP] alone with 
    other language properties into definition [wd] below, and use [wd] instead of [wdFP]
    in corresponding theorems/lemmas *) 
Record wd (L: Language): Prop :=
  {
    step_forward: corestep_forward (step L);
    step_local_eff: corestep_local_eff (step L);
    step_locality_1: corestep_locality_1 (step L);
    step_locality_2: corestep_locality_2 (step L);

    init_gmem_valid: init_gmem_valid' (init_gmem L);
    eq_mem_step: eq_mem_eq_corestep (step L);
    step_not_atext: corestep_not_at_external (step L) (at_external L);
    step_not_halt: corestep_not_halted (step L) (halt L);
    atext_not_halt: at_external_halted_excl (at_external L) (halt L);
  }.

Lemma wd_wdFP: forall L, wd L -> wdFP L.
Proof. intros; destruct H; constructor; auto. Qed.

Definition lang_det (lang: Language) : Prop :=
  step_det lang.(@step).

Definition mod_det (md: ModSem.t) : Prop :=
  lang_det (ModSem.lang md).

Definition mod_wd (md: ModSem.t) : Prop :=
  wd (ModSem.lang md).

Section steps.
  Context {C M: Type}.
  Variable step: C -> M -> FP.t -> C -> M -> Prop.

  Inductive star: C -> M -> FP.t -> C -> M -> Prop :=
  | star_refl: forall c m, star c m FP.emp c m
  | star_step: forall c m fp c' m' fp' c'' m'',
      step c m fp c' m' ->
      star c' m' fp' c'' m'' ->
      star c m (FP.union fp fp') c'' m''.

  Lemma star_one:
    forall c m fp c' m',
      step c m fp c' m' ->
      star c m fp c' m'.
  Proof.
    intros.
    rewrite <- (FP.emp_union_fp fp), FP.union_comm_eq.
    econstructor; eauto. constructor.
  Qed.

  Lemma star_two:
    forall c1 m1 fp1 c2 m2 fp2 c3 m3 fp,
      step c1 m1 fp1 c2 m2 ->
      step c2 m2 fp2 c3 m3 ->
      fp = FP.union fp1 fp2 ->
      star c1 m1 fp c3 m3.
  Proof.
    intros. subst fp.
    econstructor; eauto.
    apply star_one. auto.
  Qed.

  Lemma star_three:
    forall c1 m1 fp1 c2 m2 fp2 c3 m3 fp3 c4 m4 fp,
      step c1 m1 fp1 c2 m2 ->
      step c2 m2 fp2 c3 m3 ->
      step c3 m3 fp3 c4 m4 ->
      fp = FP.union fp1 (FP.union fp2 fp3) ->
      star c1 m1 fp c4 m4.
  Proof.
    intros. subst fp.
    econstructor; eauto.
    eapply star_two; eauto.
  Qed.

  Lemma star_four:
    forall c1 m1 fp1 c2 m2 fp2 c3 m3 fp3 c4 m4 fp4 c5 m5 fp,
      step c1 m1 fp1 c2 m2 ->
      step c2 m2 fp2 c3 m3 ->
      step c3 m3 fp3 c4 m4 ->
      step c4 m4 fp4 c5 m5 ->
      fp = FP.union fp1 (FP.union fp2 (FP.union fp3 fp4)) ->
      star c1 m1 fp c5 m5.
  Proof.
    intros. subst fp.
    econstructor; eauto.
    eapply star_three; eauto.
  Qed.
  
  Lemma star_trans:
    forall c1 m1 fp1 c2 m2,
      star c1 m1 fp1 c2 m2 ->
      forall fp2 c3 m3 fp,
        star c2 m2 fp2 c3 m3 ->
        fp = FP.union fp1 fp2 ->
        star c1 m1 fp c3 m3.
  Proof.
    induction 1; intros.
    rewrite H0. rewrite FP.emp_union_fp. auto.
    rewrite H2. rewrite <- FP.fp_union_assoc. eapply star_step; eauto.
  Qed.
  
  Lemma star_left:
    forall c1 m1 fp1 c2 m2 fp2 c3 m3 fp,
      step c1 m1 fp1 c2 m2 ->
      star c2 m2 fp2 c3 m3 ->
      fp = FP.union fp1 fp2 ->
      star c1 m1 fp c3 m3.
  Proof.
    intros. subst. econstructor; eauto.
  Qed.

  Lemma star_right:
    forall c1 m1 fp1 c2 m2 fp2 c3 m3 fp,
      star c1 m1 fp1 c2 m2 ->
      step c2 m2 fp2 c3 m3 ->
      fp = FP.union fp1 fp2 ->
      star c1 m1 fp c3 m3 .
  Proof.
    intros. subst. eapply star_trans; eauto.
    apply star_one. auto.
  Qed.
  
  Inductive plus: C -> M -> FP.t -> C -> M -> Prop :=
  | plus_one: forall c m fp c' m',
      step c m fp c' m' ->
      plus c m fp c' m'
  | plus_cons: forall c m fp c' m' fp' c'' m'',
      step c m fp c' m' ->
      plus c' m' fp' c'' m'' ->
      plus c m (FP.union fp fp') c'' m''.

  Lemma plus_left:
    forall c1 m1 fp1 c2 m2 fp2 c3 m3 fp,
      step c1 m1 fp1 c2 m2 ->
      star c2 m2 fp2 c3 m3 ->
      fp = FP.union fp1 fp2 ->
      plus c1 m1 fp c3 m3.
  Proof.
    intros until 2.
    generalize dependent H.
    generalize dependent fp.
    generalize dependent fp1.
    generalize dependent m1.
    generalize dependent c1.
    
    induction H0; intros. subst fp.
    rewrite FP.fp_union_emp. constructor. auto.
    subst. eapply plus_cons; eauto.
  Qed.

  Lemma plus_two:
    forall c1 m1 fp1 c2 m2 fp2 c3 m3 fp,
      step c1 m1 fp1 c2 m2 ->
      step c2 m2 fp2 c3 m3 ->
      fp = FP.union fp1 fp2 ->
      plus c1 m1 fp c3 m3.
  Proof.
    intros. subst. eapply plus_cons; eauto.
    apply plus_one; auto.
  Qed.

  Lemma plus_three:
     forall c1 m1 fp1 c2 m2 fp2 c3 m3 fp3 c4 m4 fp,
      step c1 m1 fp1 c2 m2 ->
      step c2 m2 fp2 c3 m3 ->
      step c3 m3 fp3 c4 m4 ->      
      fp = FP.union fp1 (FP.union fp2 fp3)->
      plus c1 m1 fp c4 m4.
  Proof.
    intros. subst. eapply plus_cons; eauto.
    eapply plus_two; eauto.
  Qed.

  Lemma plus_four:
    forall c1 m1 fp1 c2 m2 fp2 c3 m3 fp3 c4 m4 fp4 c5 m5 fp,
      step c1 m1 fp1 c2 m2 ->
      step c2 m2 fp2 c3 m3 ->
      step c3 m3 fp3 c4 m4 ->
      step c4 m4 fp4 c5 m5 ->
      fp = FP.union fp1 (FP.union fp2 (FP.union fp3 fp4))->
      plus c1 m1 fp c5 m5.
  Proof.
    intros. subst. eapply plus_cons; eauto.
    eapply plus_three; eauto.
  Qed.

  Lemma plus_star:
    forall c m fp c' m',
      plus c m fp c' m' ->
      star c m fp c' m'.
  Proof.
    intros. induction H.
    apply star_one; auto.
    eapply star_step; eauto.
  Qed.

  Lemma plus_right:
    forall c1 m1 fp1 c2 m2 fp2 c3 m3 fp,
      star c1 m1 fp1 c2 m2 ->
      step c2 m2 fp2 c3 m3 ->
      fp = FP.union fp1 fp2 ->
      plus c1 m1 fp c3 m3.
  Proof.
    intros.
    generalize dependent fp.
    generalize dependent H0.
    generalize dependent m3.
    generalize dependent c3.
    generalize dependent fp2.
    induction H; intros; subst.
    rewrite FP.emp_union_fp. apply plus_one. auto.
    rewrite <- FP.fp_union_assoc. eapply plus_cons; eauto.
  Qed.

  Lemma plus_left':
    forall c1 m1 fp1 c2 m2 fp2 c3 m3 fp,
      step c1 m1 fp1 c2 m2 ->
      plus c2 m2 fp2 c3 m3 ->
      fp = FP.union fp1 fp2 ->
      plus c1 m1 fp c3 m3.
  Proof.
    intros. subst. eapply plus_cons; eauto.
  Qed.

  Lemma plus_right':
    forall c1 m1 fp1 c2 m2 fp2 c3 m3 fp,
      plus c1 m1 fp1 c2 m2 ->
      step c2 m2 fp2 c3 m3 ->
      fp = FP.union fp1 fp2 ->
      plus c1 m1 fp c3 m3.
  Proof.
    intros. apply plus_star in H.
    eapply plus_right; eauto.
  Qed.

  Lemma plus_star_trans:
    forall c1 m1 fp1 c2 m2 fp2 c3 m3 fp,
      plus c1 m1 fp1 c2 m2 ->
      star c2 m2 fp2 c3 m3 ->
      fp = FP.union fp1 fp2 ->
      plus c1 m1 fp c3 m3.
  Proof.
    intros until 1.
    generalize H fp2 c3 m3 fp. clear. induction 1; intros; subst.
    eapply plus_left; eauto.
    rewrite <- FP.fp_union_assoc.
    eapply plus_cons; eauto.
  Qed.

  Lemma star_plus_trans:
    forall c1 m1 fp1 c2 m2 fp2 c3 m3 fp,
      star c1 m1 fp1 c2 m2 ->
      plus c2 m2 fp2 c3 m3 ->
      fp = FP.union fp1 fp2 ->
      plus c1 m1 fp c3 m3.
  Proof.
    intros until 1.
    generalize H fp2 c3 m3 fp. clear. induction 1; intros; subst.
    rewrite FP.emp_union_fp. auto.
    rewrite <- FP.fp_union_assoc.
    eapply plus_cons; eauto.
  Qed.

  Lemma plus_trans:
    forall c1 m1 fp1 c2 m2 fp2 c3 m3 fp,
      plus c1 m1 fp1 c2 m2 ->
      plus c2 m2 fp2 c3 m3 ->
      fp = FP.union fp1 fp2 ->
      plus c1 m1 fp c3 m3.
  Proof.
    intros. apply plus_star in H. eapply star_plus_trans; eauto.
  Qed.

  Lemma plus_inv:
    forall c m fp c' m',
      plus c m fp c' m' ->
      step c m fp c' m' \/
      exists c0 m0 fp0 fp', step c m fp0 c0 m0 /\ plus c0 m0 fp' c' m' /\ fp = FP.union fp0 fp'.
  Proof.
    intros.
    inversion H; subst.
    left. auto.
    right. do 4 eexists. split; eauto.
  Qed.

  Lemma star_inv:
    forall c m fp c' m',
      star c m fp c' m' ->
      (c = c' /\ m = m' /\ fp = FP.emp) \/ plus c m fp c' m'.
  Proof.
    intros.
    inversion H; subst; auto.
    right. eapply plus_left; eauto.
  Qed.
      
    
End steps.