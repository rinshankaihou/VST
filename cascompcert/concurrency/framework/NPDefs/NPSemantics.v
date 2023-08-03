Require Import Coqlib AST Values.
Require Import Blockset Footprint GMemory InteractionSemantics GAST GlobDefs ETrace Injections.

(** * Non-preemptive Global Semantics *)

(** This file defines the non-preemptive global semantics. Threads would not switch
    until exiting an atomic block, print event or thread halting. 
    See [Ext_Atom], [EF_Print] and [Thrd_Halt], 
    where the [cur_tid] of resulting configuration could be arbitrary valid thread that is not halted.
    Other rules are the same comparing with preemptive global semantics,
    except that there is no [Sw] rules such that the switching points are confined to the three cases above.
*)

Section NPSem.
  Context {GE: GlobEnv.t}.

  Inductive np_step : ProgConfig -> glabel -> FP.t -> ProgConfig -> Prop :=
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
          np_step (Build_ProgConfig GE thdp t gm d) tau fp
                  (Build_ProgConfig GE thdp' t gm' d)
  
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
            np_step (Build_ProgConfig GE thdp t gm O) tau FP.emp
                    (Build_ProgConfig GE thdp' t gm O)

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
            np_step (Build_ProgConfig GE thdp t gm O) tau FP.emp
                    (Build_ProgConfig GE thdp'' t gm O)

  | Thrd_Halt :
      forall thdp t gm c res thdp' t',
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
          (H_thread_halt: ThreadPool.halted thdp' t)
          (* switch to a valid thread *)
          (H_thread_valid: ThreadPool.valid_tid thdp' t')
          (H_not_halted: ~ ThreadPool.halted thdp' t'),
          (* ===================================================== *)
          np_step (Build_ProgConfig GE thdp t gm O) sw FP.emp
                  (Build_ProgConfig GE thdp' t' gm O)

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
          (H_thread_halt: ThreadPool.halted thdp' t)
          (* all thread halted *)
          (H_all_thread_halted: forall t', ThreadPool.valid_tid thdp' t' -> ThreadPool.halted thdp' t'),
          (* ===================================================== *)
          np_step (Build_ProgConfig GE thdp t gm O) tau FP.emp
                  (Build_ProgConfig GE thdp' t gm O)
  
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
            np_step (Build_ProgConfig GE thdp t gm O) tau FP.emp
                      (Build_ProgConfig GE thdp' t gm I)
 
  | Ext_Atom :
       forall thdp t gm c cc' c' thdp' t',
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
          (H_tp_upd: ThreadPool.update thdp t c' thdp')
          (* switch to a valid thread *)
          (H_thread_valid: ThreadPool.valid_tid thdp' t')
          (H_not_halted: ~ ThreadPool.halted thdp' t'),
          (* ===================================================== *)
            np_step (Build_ProgConfig GE thdp t gm I) sw FP.emp
                      (Build_ProgConfig GE thdp' t' gm O)

  | EF_Print :
      forall thdp t gm c v cc' c' thdp' t',
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
          (H_tp_upd: ThreadPool.update thdp t c' thdp')
          (* switch to a valid thread *)
          (H_thread_valid: ThreadPool.valid_tid thdp' t')
          (H_not_halted: ~ ThreadPool.halted thdp' t'),
          (* ===================================================== *)
          np_step (Build_ProgConfig GE thdp t gm O) (evt v) FP.emp
                    (Build_ProgConfig GE thdp' t' gm O).
  
  
  (** Abort if current thread got stuck *)
  Definition np_abort (pc: @ProgConfig GE) : Prop :=
    (~ final_state pc) /\
    (forall gl fp pc', ~ np_step pc gl fp pc').
  
End NPSem.

CoInductive np_safe_config {ge : GlobEnv.t} (s: @ProgConfig ge) : Prop :=
| NP_safe_config: ~ np_abort s ->
                  (forall l fp s', np_step s l fp s' -> np_safe_config s') ->
                  np_safe_config s.

Inductive np_safe_prog {NL: nat} {L: @langs NL} (p: prog L) (*(root: Bset.t)*) : Prop :=
| NP_safe_prog:
    (forall gm ge s t, init_config p gm ge s t -> np_safe_config s) ->
    np_safe_prog p.

(** Refinement between non-preemptive program configurations,
    i.e. subset of event trace *)
Definition np_config_refine {ge1 ge2: GlobEnv.t}
           (s1: @ProgConfig ge1) (s2: @ProgConfig ge2) : Prop :=
  forall B, Etr np_step np_abort final_state s1 B ->
            Etr np_step np_abort final_state s2 B.

(** Refinement between non-preemptive programs *)
Inductive np_prog_refine {NL: nat} {L: @langs NL}:
  prog L -> prog L -> Prop :=
| NP_Prog_Refine: forall pSrc pTgt,
    (forall mu sgm sge spc tgm tge tpc t,
        InitRel mu sge tge sgm tgm ->
        init_config pSrc sgm sge spc t ->
        init_config pTgt tgm tge tpc t ->
        (* target refine source *)
        np_config_refine tpc spc 
    ) ->
    np_prog_refine pSrc pTgt.




    