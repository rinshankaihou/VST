From mathcomp.ssreflect Require Import fintype.
Require Import Coqlib Maps.
Require Import AST Integers Floats Values Events Globalenvs Smallstep.

Require Import Asm.

Require Import CUAST.

Require Import Footprint GMemory FMemory TSOMem.
Require Import GAST GlobDefs ETrace Blockset.
Require Import loadframe.

Require Import ASM_local.
Require Import AsmLang.
Require Import AsmTSO.

Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.

Require Import Coq.Lists.Streams.


(** * x86 TSO program *)
Definition tsoprog : Type := (list comp_unit) * entries.

(** * x86 TSO Global Semantics *)
Inductive tsoglabel : Type :=
| tau
| sw
| ub (t: tid)
| evt (v: val).


Module TSOGlobEnv.
  Record t : Type :=
    {
      M: nat;
      modules : 'I_M -> genv;
      get_mod : ident -> option (fintype.ordinal M);
      ge_bound : block;
      freelists : FLists.t
    }.

  (** The [GE] is properly initialized from [cus] if [init cus GE] *)
  Record init (cus: list comp_unit) (GE: t): Prop :=
    {
      (** Amount of runtime semantic modules is equal to amount of compilation units *)
      mod_num: (M GE) = length cus
      ;
      (** All ges are properly initialized w.r.t. the comp unit *)
      ge_init: forall (i: 'I_(M GE)),
          (exists cui, nth_error cus i = Some cui /\
                  AsmTSO.init_genv cui (modules GE i))
      ;
      (** Domain of [get_mod] contains all internal functions *)
      get_mod_init:
        forall id mid,
          (get_mod GE id) = Some mid <->
          snd (@fold_left (nat * (option nat)) comp_unit
                          (fun ir cui => let (i, res) := ir in
                                      if res then (S i, res)
                                      else if In_dec peq id (internal_fn cui)
                                           then (S i, Some i)
                                           else (S i, res))
                          cus (0%nat, None))
          = Some (nat_of_ord mid)
      ;
    }.

  Inductive init_mem : t -> gmem -> Prop :=
    Init_mem : forall GE gm,
      (forall i : 'I_(M GE), AsmTSO.init_gmem (modules GE i) gm) ->
      (forall fi : fid, MemAux.no_overlap (FLists.get_fl (freelists GE) fi) (MemAux.valid_block_bset gm)) ->
      init_mem GE gm.
  
End TSOGlobEnv.

Module TSOCore.
  Record t {GE: TSOGlobEnv.t} : Type :=
    {
      i : 'I_(TSOGlobEnv.M GE);
      c : core;
      sg : signature;
      F: fid
    }.

  Inductive update {GE: TSOGlobEnv.t} (x: t) (cc: core) : @t GE -> Prop :=
    Update: forall x', x' = {| i := i x; c := cc; sg := sg x; F := F x |} ->
                  update x cc x'.
            
End TSOCore.
      
Module TSOThrdPool.
  Record t {GE: TSOGlobEnv.t} : Type :=
    {
      content : PMap.t (option (list (@TSOCore.t GE)));
      next_tid : tid;
      next_fmap : tid -> nat;
    }.

  Inductive update {GE: TSOGlobEnv.t} (thdp: t) (i: tid) (c': TSOCore.t) : t -> Prop :=
    Update: forall c cs thdp',
      PMap.get i (content thdp) = Some (c :: cs) ->
      thdp' = Build_t GE (PMap.set i (Some (c' :: cs)) (content thdp))
                      (next_tid thdp)
                      (next_fmap thdp) ->
      update thdp i c' thdp'.

  Definition push {GE: TSOGlobEnv.t} (thdp: t) (i: tid)
             (mid: 'I_(TSOGlobEnv.M GE))
             (cc: core)
             (sg: signature)
    : option t :=
    match (content thdp) !! i with
    | Some cs =>
      Some (Build_t
              GE
              (PMap.set i
                        (Some (TSOCore.Build_t
                                 GE mid cc sg
                                 (FLists.get_tfid (TSOGlobEnv.freelists GE) i (next_fmap thdp i))
                              :: cs )
                        )
                        (content thdp))
              (next_tid thdp)
              (fun i' => if peq i i' then ((next_fmap thdp i) + 1)%nat else next_fmap thdp i'))
    | None => None
    end.

  Definition pop {GE: TSOGlobEnv.t} (thdp: @t GE) (i: tid) : option t :=
    match (content thdp) !! i with
    | Some (c :: cs) =>
      Some {| content := PMap.set i (Some cs) (content thdp);
              next_tid := next_tid thdp;
              next_fmap := next_fmap thdp |}
    | _ => None
    end.

  Definition emp {GE: TSOGlobEnv.t} : t := Build_t GE (PMap.init None) 1%positive (fun _ => 0%nat).
  
  Definition spawn {GE: TSOGlobEnv.t}
             (thdp: t)
             (mid: 'I_(TSOGlobEnv.M GE))
             (c: AsmTSO.core)
             (sg: signature) : t :=
    let: nf := (thdp.(next_fmap) thdp.(next_tid)) in
    let: f := FLists.get_tfid (TSOGlobEnv.freelists GE) (thdp.(next_tid)) nf in
    let: c := TSOCore.Build_t GE mid c sg f in
    Build_t GE (PMap.set thdp.(next_tid) (Some (c::nil)) thdp.(content))
            (Pos.succ thdp.(next_tid))
            (fun i => if peq i thdp.(next_tid) then (S (thdp.(next_fmap) i))
                   else thdp.(next_fmap) i).

  Inductive init {GE: TSOGlobEnv.t} : entries -> t -> Prop :=
  | init_nil : init nil emp
  | init_cons :
      forall funid m_id,
        TSOGlobEnv.get_mod GE funid = Some m_id ->
        forall e thdp cc,
          init e thdp ->
          let: ge := TSOGlobEnv.modules GE m_id in
          AsmTSO.init_core ge funid nil = Some cc ->
          let: thdp':= spawn thdp m_id cc signature_main in
          init (funid :: e) thdp'.

  Inductive halted {GE: TSOGlobEnv.t} (thdp: @t GE) (i: tid) : Prop :=
  | Halted:
      PMap.get i (content thdp) = Some nil ->
      halted thdp i.

  Definition valid_tid {GE: TSOGlobEnv.t} (thdp: @t GE) (i: tid) : Prop :=
    Plt i (next_tid thdp).
  
End TSOThrdPool.

Record TSOProgConfig {GE: TSOGlobEnv.t} : Type :=
  {
    thrdpool: @TSOThrdPool.t GE;
    cid: tid;
    tm: tsomem;
  }.
    
Section TSOGlobSem.
    
  Context {GE: TSOGlobEnv.t}.
  
  Inductive tso_globstep : TSOProgConfig -> tsoglabel -> FP.t -> TSOProgConfig -> Prop :=
  | Corestep :
      forall thdp t tm c cs fp cc' c' thdp' buf' gm' tm',
        let: cc := TSOCore.c c in
        let: c_ix := TSOCore.i c in
        let: c_f := TSOCore.F c in
        let: c_fl := FLists.get_fl (TSOGlobEnv.freelists GE) c_f in
        let: ge := TSOGlobEnv.modules GE c_ix in
        let: gm := memory tm in
        let: buf := tso_buffers tm t in
        forall
          (H_tp_core: PMap.get t (TSOThrdPool.content thdp) = Some (c :: cs))
          (H_core_step: tsostep ge c_fl cc (buf, gm) fp cc' (buf', gm'))
          (H_core_upd: TSOCore.update c cc' c')
          (H_tp_upd: TSOThrdPool.update thdp t c' thdp')
          (H_tm_upd: tm' = tsoupd tm t buf' gm')
          (H_unbuf_safe: unbuffer_safe tm'),
          (* ===================================================== *)
          tso_globstep (Build_TSOProgConfig GE thdp t tm) tau fp
                       (Build_TSOProgConfig GE thdp' t tm')

  | Unbuffer :
      forall thdp t tm tm' t',
      forall (H_tid_valid: TSOThrdPool.valid_tid thdp t')
        (H_unbuf: unbuffer tm t' = Some tm'),
        (* ===================================================== *)                  
        tso_globstep (Build_TSOProgConfig GE thdp t tm) (ub t') FP.emp
                     (Build_TSOProgConfig GE thdp t tm')
        
  | Call :
      forall thdp t tm c cs funid sg args new_ix cc' thdp',
        let: cc := TSOCore.c c in
        let: c_ix := TSOCore.i c in
        let: ge := TSOGlobEnv.modules GE c_ix in
        forall
          (H_tp_core: PMap.get t (TSOThrdPool.content thdp) = Some (c :: cs))
          (H_core_atext: at_external ge cc = Some (funid, sg, args))
          (H_not_prim: not_primitive funid)
          (H_mod_id: TSOGlobEnv.get_mod GE funid = Some new_ix),
          (* init new core with funid *)
          let: new_ge := TSOGlobEnv.modules GE new_ix in
          forall
            (H_new_core: init_core new_ge funid args = Some cc')
            (H_tp_push: TSOThrdPool.push thdp t new_ix cc' sg = Some thdp'),
            (* ===================================================== *)
            tso_globstep (Build_TSOProgConfig GE thdp t tm) tau FP.emp
                      (Build_TSOProgConfig GE thdp' t tm)

  | Return :
      forall thdp t tm c cs res thdp' c' cc'' c'' thdp'',
        let: cc := TSOCore.c c in
        let: c_ix := TSOCore.i c in
        let: c_sg := TSOCore.sg c in
        let: ge := TSOGlobEnv.modules GE c_ix in
        forall
          (H_tp_core: PMap.get t (TSOThrdPool.content thdp) = Some (c :: c' :: cs))
          (H_core_halt: halt cc = Some res)
          (H_tp_pop: TSOThrdPool.pop thdp t = Some thdp'),
          let: cc' := TSOCore.c c' in
          let: c'_ix := TSOCore.i c' in
          let: ge' := TSOGlobEnv.modules GE c'_ix in
          forall
            (H_core_aftext: after_external cc' (res_sg c_sg res) = Some cc'')
            (H_core_upd: TSOCore.update c' cc'' c'')
            (H_tp_upd: TSOThrdPool.update thdp' t c'' thdp''),
            (* ===================================================== *)
            tso_globstep (Build_TSOProgConfig GE thdp t tm) tau FP.emp
                      (Build_TSOProgConfig GE thdp'' t tm)

  | Halt :
      forall thdp t tm c res thdp',
        let: cc := TSOCore.c c in
        let: c_ix := TSOCore.i c in
        let: c_sg := TSOCore.sg c in
        let: ge := TSOGlobEnv.modules GE c_ix in
        forall
          (H_tp_core: PMap.get t (TSOThrdPool.content thdp) = Some (c :: nil))
          (H_core_halt: halt cc = Some res)
          (H_tp_pop: TSOThrdPool.pop thdp t = Some thdp'),
          (* ===================================================== *)
          tso_globstep (Build_TSOProgConfig GE thdp t tm) tau FP.emp
                      (Build_TSOProgConfig GE thdp' t tm)
  
  | EF_Print :
      forall thdp t tm c cs v cc' c' thdp',
        let: cc := TSOCore.c c in
        let: c_ix := TSOCore.i c in
        let: ge := TSOGlobEnv.modules GE c_ix in
        forall
          (H_tp_core: PMap.get t (TSOThrdPool.content thdp) = Some (c :: cs))
          (H_core_atext: at_external ge cc = Some (print, print_sg, v::nil))
          (H_v: not_pointer v)
          (H_core_aftext: after_external cc None = Some cc')
          (H_core_update: TSOCore.update c cc' c')
          (H_tp_upd: TSOThrdPool.update thdp t c' thdp'),
          (* ===================================================== *)
          tso_globstep (Build_TSOProgConfig GE thdp t tm) (evt v) FP.emp
                       (Build_TSOProgConfig GE thdp' t tm)
  
  | Switch :
      forall thdp t tm t'
        (H_thread_valid: TSOThrdPool.valid_tid thdp t')
        (H_not_halted: ~ TSOThrdPool.halted thdp t'),
        (* ====================================================== *)
        tso_globstep (Build_TSOProgConfig GE thdp t tm) sw FP.emp
                  (Build_TSOProgConfig GE thdp t' tm).


  (* Abort if current thread got stuck or 
     buffer item cannot be applied. *)
  Definition abort (pc: @TSOProgConfig GE) : Prop :=
    (~ TSOThrdPool.halted (pc.(thrdpool)) (pc.(cid)) 
     /\ (forall t, tso_buffers pc.(tm) t = nil)
     /\ (forall gl fp pc', tso_globstep pc gl fp pc' -> gl = sw))
    \/
    (exists t, tso_buffers (pc.(tm)) t <> nil /\ unbuffer (pc.(tm)) t = None).

  Inductive final_state {GE: TSOGlobEnv.t} : @TSOProgConfig GE -> Prop :=
    Final_state : forall pc thdp,
      thrdpool pc = thdp ->
      (forall i, TSOThrdPool.valid_tid thdp i ->
            TSOThrdPool.halted thdp i /\
            tso_buffers (pc.(tm)) i = nil) ->
      final_state pc.
        
End TSOGlobSem.

Definition tsoglabel_to_glabel (l: tsoglabel) : glabel :=
  match l with
  | ub _ | tau => ETrace.tau
  | sw => ETrace.sw
  | evt v => ETrace.evt v
  end.

Inductive tso_etrstep {GE: TSOGlobEnv.t} :
  TSOProgConfig -> glabel -> footprint -> TSOProgConfig -> Prop :=
  TSO_Etrstep:
    forall pc l fp pc',
      @tso_globstep GE pc l fp pc' ->
      tso_etrstep pc (tsoglabel_to_glabel l) fp pc'.

Inductive tsoEtr {GE: TSOGlobEnv.t} (s: TSOProgConfig) : behav -> Prop :=
  TSOEtr : forall B, Etr (@tso_etrstep GE) abort final_state s B ->
                tsoEtr s B.

Inductive tso_initconfig (p: tsoprog) (gm: gmem) (GE: TSOGlobEnv.t) (pc: @TSOProgConfig GE) (t: tid) : Prop :=
  TSO_initconfig:
    TSOGlobEnv.init (fst p) GE ->
    TSOGlobEnv.init_mem GE gm ->
    TSOThrdPool.init (snd p) (thrdpool pc) ->
    FLists.wd (TSOGlobEnv.freelists GE) ->
    (forall fi, MemAux.no_overlap (FLists.get_fl (TSOGlobEnv.freelists GE) fi)
                             (MemAux.valid_block_bset gm)) ->
    MemClosures.reach_closed gm (MemAux.valid_block_bset gm) ->
    cid pc = t ->
    Plt t (TSOThrdPool.next_tid (thrdpool pc)) ->
    tm pc = tsomem_init gm ->
    tso_initconfig p gm GE pc t.


(** relation between client src/tgt genvs, require eq on gvars *)
Record genv_match F V (sge: Genv.t F V) (tge: genv): Prop :=
  {
    genv_public_eq: forall id, In id (Genv.genv_public sge) <-> In id (Genv.genv_public tge);
    genv_symb_eq: forall id, PTree.get id (Genv.genv_symb sge) = PTree.get id (Genv.genv_symb tge);
    genv_defs_match: forall id b b', PTree.get id (Genv.genv_symb sge) = Some b ->
                                PTree.get id (Genv.genv_symb tge) = Some b' ->
                                option_rel (LDSimDefs.globdef_match)
                                           (PTree.get b (Genv.genv_defs sge))
                                           (PTree.get b' (Genv.genv_defs tge));
    genv_next_eq: Genv.genv_next sge = Genv.genv_next tge;
  }.

Require Import RGRels.
Record tso_sc_initRel (SGE: GlobEnv.t) (TGE: TSOGlobEnv.t) (sgm tgm: gmem) : Prop :=
  {
    init_rel_gm_eq: forall b ofs,
      ~ obj_mem sgm b ofs -> eq_on_loc b ofs sgm tgm;
    init_rel_sgm_sep: sep_obj_client_block sgm;
    init_rel_ge_bound: GlobEnv.ge_bound SGE = TSOGlobEnv.ge_bound TGE;
    init_rel_freelists: GlobEnv.freelists SGE = TSOGlobEnv.freelists TGE;
    init_rel_get_mod: forall id,
        option_rel (fun x y => nat_of_ord x = nat_of_ord y)
                   (GlobEnv.get_mod SGE id) (TSOGlobEnv.get_mod TGE id);
    init_rel_ge_match: forall ix ix',
        nat_of_ord ix = nat_of_ord ix' ->
        genv_match _ _
                   (InteractionSemantics.ModSem.ge (GlobEnv.modules SGE ix))
                   (TSOGlobEnv.modules TGE ix');

  }.

Require GlobSemantics.


(** refinement holds for executions that do not silently diverge *)
CoInductive notsd : behav -> Prop :=
| nsd_done : notsd Behav_done
| nsd_abort : notsd Behav_abort
| nsd_cons : forall v B, notsd B -> notsd (Behav_cons v B).

Inductive tso_refine_sc
          {NL: nat} {L: @langs NL} : @prog NL L -> tsoprog -> Prop :=
| TSOProg_Refine_SC:
    forall pSC pTSO,
      (forall sgm sge spc t tgm tge tpc,
          tso_sc_initRel sge tge sgm tgm ->
          init_config pSC sgm sge spc t ->
          ~ DRF.star_race_config spc ->
          safe_state GlobSemantics.glob_step GlobSemantics.abort spc ->
          tso_initconfig pTSO tgm tge tpc t ->
          (forall B, tsoEtr tpc B ->
                notsd B ->
                Etr GlobSemantics.glob_step GlobSemantics.abort GlobDefs.final_state spc B)
      )
      ->
      tso_refine_sc pSC pTSO.



