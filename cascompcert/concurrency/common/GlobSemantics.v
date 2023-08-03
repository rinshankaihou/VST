Require Import Coqlib Maps.
Require Import AST Values.
Require Import Footprint GMemory InteractionSemantics GAST GlobDefs ETrace Blockset Injections.
Require Import Coq.Lists.Streams.

(** This file defines the global semantics of a program. *)

(** * Global Semantics *)

Section GlobSem.
  Context {GE: GlobEnv.t}.

  (** The global semantics rules *)
  Inductive glob_step : ProgConfig -> glabel -> FP.t -> ProgConfig -> Prop :=
  (** Normal core-step *)
  | Corestep :
      forall thdp t gm d c fp cc' c' thdp' gm',
        let: cc := Core.c c in
        let: c_ix := Core.i c in
        let: c_f := Core.F c in
        let: c_fl := FLists.get_fl (GlobEnv.freelists GE) c_f in
        let: c_mod := GlobEnv.modules GE c_ix in
        let: c_lang := ModSem.lang c_mod in
        let: Ge := ModSem.Ge c_mod in
        forall
          (H_tp_core: ThreadPool.get_top thdp t = Some c)
          (H_core_step: step c_lang Ge c_fl cc gm fp cc' gm')
          (H_core_upd: Core.update c cc' c')
          (H_tp_upd: ThreadPool.update thdp t c' thdp'),
          (* ===================================================== *)
          glob_step (Build_ProgConfig GE thdp t gm d) tau fp
                    (Build_ProgConfig GE thdp' t gm' d)
  (** Steps that call external function:
      when the current core generates an [at_external] event with the 
      function id [funid] and arguments [args],
      the global semantics find the module [new_mod] corresponds to [funid] using 
      [GlobEnv.get_mod] function, and 
      initialize a new core using [init_core] of [new_mod] with [funid] and [args],
      and pushes the new core using [ThreadPool.push] into the call stack of current thread
   *)
  | Call :
      forall thdp t gm c funid sg args new_ix cc' thdp',
        let: cc := Core.c c in
        let: c_ix := Core.i c in
        let: c_mod := GlobEnv.modules GE c_ix in
        let: c_lang := ModSem.lang c_mod in
        let: Ge := ModSem.Ge c_mod in
        forall
          (H_tp_core: ThreadPool.get_top thdp t = Some c)
          (H_core_atext: at_external c_lang Ge cc = Some (funid, sg, args))
          (H_not_prim: not_primitive funid)
          (H_mod_id: GlobEnv.get_mod GE funid = Some new_ix),
          (* init new core with funid *)
          let: new_mod := GlobEnv.modules GE new_ix in
          let: new_lang := ModSem.lang new_mod in
          let: new_Ge := ModSem.Ge new_mod in
          forall
            (H_new_core: init_core new_lang new_Ge funid args = Some cc')
            (H_tp_push: ThreadPool.push thdp t new_ix cc' sg = Some thdp'),
            (* ===================================================== *)
            glob_step (Build_ProgConfig GE thdp t gm O) tau FP.emp
                      (Build_ProgConfig GE thdp' t gm O)
  (** Steps of returning of external function:
      when the current core halts with return value [res],
      the global semantics pops the current core using [ThreadPool.pop],
      and updates the caller core using [after_external] with the return value.
   *)
  | Return :
      forall thdp t gm c res thdp' c' cc'' c'' thdp'',
        let: cc := Core.c c in
        let: c_ix := Core.i c in
        let: c_sg := Core.sg c in
        let: c_mod := GlobEnv.modules GE c_ix in
        let: c_lang := ModSem.lang c_mod in
        let: Ge := ModSem.Ge c_mod in
        forall
          (H_tp_core: ThreadPool.get_top thdp t = Some c)
          (H_core_halt: halt c_lang cc = Some res)
          (H_tp_pop: ThreadPool.pop thdp t = Some thdp')
          (H_tp_caller: ThreadPool.get_top thdp' t = Some c'),
          let: cc' := Core.c c' in
          let: c'_ix := Core.i c' in
          let: c'_mod := GlobEnv.modules GE c'_ix in
          let: c'_lang := ModSem.lang c'_mod in
          let: Ge' := ModSem.Ge c'_mod in
          forall
            (H_core_aftext: after_external c'_lang cc' (res_sg c_sg res) = Some cc'')
            (H_core_upd: Core.update c' cc'' c'')
            (H_tp_upd: ThreadPool.update thdp' t c'' thdp''),
            (* ===================================================== *)
            glob_step (Build_ProgConfig GE thdp t gm O) tau FP.emp
                      (Build_ProgConfig GE thdp'' t gm O)
  (** Thread halt *)
  | Halt :
      forall thdp t gm c res thdp',
        let: cc := Core.c c in
        let: c_ix := Core.i c in
        let: c_sg := Core.sg c in
        let: c_mod := GlobEnv.modules GE c_ix in
        let: c_lang := ModSem.lang c_mod in
        let: Ge := ModSem.Ge c_mod in
        forall
          (H_tp_core: ThreadPool.get_top thdp t = Some c)
          (H_core_halt: halt c_lang cc = Some res)
          (H_tp_pop: ThreadPool.pop thdp t = Some thdp')
          (H_thread_halt:ThreadPool.halted thdp' t),
          (* ===================================================== *)
            glob_step (Build_ProgConfig GE thdp t gm O) tau FP.emp
                      (Build_ProgConfig GE thdp' t gm O)
  (** Enter atomic block *)
  | Ent_Atom :
      forall thdp t gm c cc' c' thdp',
        let: cc := Core.c c in
        let: c_ix := Core.i c in
        let: c_mod := GlobEnv.modules GE c_ix in
        let: c_lang := ModSem.lang c_mod in
        let: Ge := ModSem.Ge c_mod in
        forall
          (H_tp_core: ThreadPool.get_top thdp t = Some c)
          (H_core_atext: at_external c_lang Ge cc = Some (ent_atom, ent_atom_sg, nil))
          (H_core_aftext: after_external c_lang cc None = Some cc')
          (H_core_update: Core.update c cc' c')
          (H_tp_upd: ThreadPool.update thdp t c' thdp'),
          (* ===================================================== *)
            glob_step (Build_ProgConfig GE thdp t gm O) tau FP.emp
                      (Build_ProgConfig GE thdp' t gm I)
  (** Exit atomic block *)
  | Ext_Atom :
       forall thdp t gm c cc' c' thdp',
        let: cc := Core.c c in
        let: c_ix := Core.i c in
        let: c_mod := GlobEnv.modules GE c_ix in
        let: c_lang := ModSem.lang c_mod in
        let: Ge := ModSem.Ge c_mod in
        forall
          (H_tp_core: ThreadPool.get_top thdp t = Some c)
          (H_core_atext: at_external c_lang Ge cc = Some (ext_atom, ext_atom_sg, nil))
          (H_core_aftext: after_external c_lang cc None = Some cc')
          (H_core_update: Core.update c cc' c')
          (H_tp_upd: ThreadPool.update thdp t c' thdp'),
          (* ===================================================== *)
            glob_step (Build_ProgConfig GE thdp t gm I) tau FP.emp
                      (Build_ProgConfig GE thdp' t gm O)
  (** Generate event *)
  | EF_Print :
      forall thdp t gm c v cc' c' thdp',
        let: cc := Core.c c in
        let: c_ix := Core.i c in
        let: c_mod := GlobEnv.modules GE c_ix in
        let: c_lang := ModSem.lang c_mod in
        let: Ge := ModSem.Ge c_mod in
        forall
          (H_tp_core: ThreadPool.get_top thdp t = Some c)
          (H_core_atext: at_external c_lang Ge cc = Some (print, print_sg, v::nil))
          (H_v: not_pointer v)
          (H_core_aftext: after_external c_lang cc None = Some cc')
          (H_core_update: Core.update c cc' c')
          (H_tp_upd: ThreadPool.update thdp t c' thdp'),
          (* ===================================================== *)
            glob_step (Build_ProgConfig GE thdp t gm O) (evt v) FP.emp
                      (Build_ProgConfig GE thdp' t gm O)
  (** Thread switch, only switch to non-halted threads *)
  | Switch :
      forall thdp t gm t'
             (H_thread_valid: ThreadPool.valid_tid thdp t')
             (H_not_halted: ~ ThreadPool.halted thdp t'),
        (* ====================================================== *)
        glob_step (Build_ProgConfig GE thdp t gm O) sw FP.emp
                  (Build_ProgConfig GE thdp t' gm O).


  (** Abort if current thread got stuck *)
  Definition abort (pc: @ProgConfig GE) : Prop :=
    (~ ThreadPool.halted (pc.(thread_pool)) (pc.(cur_tid)) ) /\
    (forall gl fp pc', glob_step pc gl fp pc' -> gl = sw).

End GlobSem.

(** A program is safe if for any initial configurations, it would not abort *)
Inductive safe_prog {NL: nat} {L: @langs NL} (p: @prog NL L) :=
  Safe_prog : (forall gm GE pc t, init_config p gm GE pc t ->
                               safe_state glob_step abort pc) ->
              safe_prog p.

(** Refinement between program configurations, i.e. subset of event traces *)
Definition config_refine {ge1 ge2: GlobEnv.t}
           (s1: @ProgConfig ge1) (s2: @ProgConfig ge2) : Prop :=
  forall B, Etr glob_step abort final_state s1 B ->
            Etr glob_step abort final_state s2 B.

(** Refinement between programs *)
Inductive prog_refine
          {NL:nat} {L: @langs NL} : @prog NL L -> @prog NL L -> Prop :=
| Prog_Refine : forall pSrc pTgt,
    (forall mu sgm sge spc ts tgm tge tpc tt,
        InitRel mu sge tge sgm tgm ->
        init_config pSrc sgm sge spc ts ->
        init_config pTgt tgm tge tpc tt ->  
        config_refine tpc spc
    ) ->
    prog_refine pSrc pTgt.
