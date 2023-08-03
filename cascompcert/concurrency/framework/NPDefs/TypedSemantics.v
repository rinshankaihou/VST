Require Import Coqlib AST Values.

Require Import Blockset Footprint GMemory InteractionSemantics GAST
        GlobDefs ETrace GlobSemantics NPSemantics Injections GDefLemmas. 

Require Import Arith Wf Classical_Prop FunctionalExtensionality.
(** This file contains auxiliary definition of non-preemptive semantics used in other proof.*)
Section typed_step.
    Context {GE:GlobEnv.t}.
    Inductive steptype:Type :=
    | core: steptype
    | call: steptype
    | ret : steptype
    | entat:steptype
    | extat:steptype
    | thrdhalt : steptype
    | allhalt: steptype      
    | efprint: steptype
    | glob_sw: steptype
    | glob_halt:steptype.
    Local Notation "{ A , B , C , D }" := (Build_ProgConfig GE A B C D).
    Inductive type_np_step : steptype->ProgConfig -> glabel -> FP.t -> ProgConfig -> Prop :=
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
            type_np_step core (Build_ProgConfig GE thdp t gm d) tau fp
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
              type_np_step call (Build_ProgConfig GE thdp t gm O) tau FP.emp
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
              type_np_step ret (Build_ProgConfig GE thdp t gm O) tau FP.emp
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
            type_np_step thrdhalt (Build_ProgConfig GE thdp t gm O) sw FP.emp
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
            type_np_step allhalt (Build_ProgConfig GE thdp t gm O) tau FP.emp
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
            type_np_step entat (Build_ProgConfig GE thdp t gm O) tau FP.emp
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
            type_np_step extat (Build_ProgConfig GE thdp t gm I) sw FP.emp
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
            type_np_step efprint (Build_ProgConfig GE thdp t gm O) (evt v) FP.emp
                         (Build_ProgConfig GE thdp' t' gm O).
    Inductive type_glob_step : steptype-> ProgConfig -> glabel -> FP.t -> ProgConfig -> Prop :=
    | GCorestep :
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
            type_glob_step core (Build_ProgConfig GE thdp t gm d) tau fp
                      (Build_ProgConfig GE thdp' t gm' d)
                      
    | GCall :
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
              type_glob_step call (Build_ProgConfig GE thdp t gm O) tau FP.emp
                        (Build_ProgConfig GE thdp' t gm O)
                        
    | GReturn :
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
              type_glob_step ret (Build_ProgConfig GE thdp t gm O) tau FP.emp
                        (Build_ProgConfig GE thdp'' t gm O)
                        
    | GHalt :
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
            type_glob_step glob_halt (Build_ProgConfig GE thdp t gm O) tau FP.emp
                      (Build_ProgConfig GE thdp' t gm O)
                      
    | GEnt_Atom :
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
            type_glob_step entat (Build_ProgConfig GE thdp t gm O) tau FP.emp
                      (Build_ProgConfig GE thdp' t gm I)
                      
    | GExt_Atom :
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
            type_glob_step extat (Build_ProgConfig GE thdp t gm I) tau FP.emp
                      (Build_ProgConfig GE thdp' t gm O)
                      
    | GEF_Print :
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
            type_glob_step efprint (Build_ProgConfig GE thdp t gm O) (evt v) FP.emp
                      (Build_ProgConfig GE thdp' t gm O)
                      
    | GSwitch :
        forall thdp t gm t'
          (H_thread_valid: ThreadPool.valid_tid thdp t')
          (H_not_halted: ~ ThreadPool.halted thdp t'),
          (* ====================================================== *)
          type_glob_step glob_sw (Build_ProgConfig GE thdp t gm O) sw FP.emp
                    (Build_ProgConfig GE thdp t' gm O).
    Corollary type_step_exists :
      forall pc l fp pc1,
        @np_step GE pc l fp pc1->
        exists type,type_np_step type pc l fp pc1.
    Proof.
      intros.
      inversion H;subst;[exists core;eapply Corestep|exists call;eapply Call|exists ret;eapply Return|exists thrdhalt;eapply Thrd_Halt|exists allhalt;eapply Halt|exists entat;eapply Ent_Atom|exists extat;eapply Ext_Atom|exists efprint;eapply EF_Print ];eauto.
    Qed.
    Corollary type_step_elim:
      forall t pc l fp pc1,
        type_np_step t pc l fp pc1 -> @np_step GE pc l fp pc1.
    Proof.
      intros.
      inversion H;subst;[econstructor 1|econstructor 2|econstructor 3|econstructor 4|econstructor 5|econstructor 6|econstructor 7|econstructor 8];eauto.
    Qed.

    Lemma tau_star_type_step:
      forall t pc fp pc1 ,
        tau_star (type_np_step t) pc fp pc1 ->
        tau_star np_step pc fp pc1.
    Proof.
      intros.
      induction H.
      constructor.
      econstructor 2;eauto.
      eapply type_step_elim;eauto.
    Qed.

    Corollary type_glob_step_exists :
      forall pc l fp pc1,
        @glob_step GE pc l fp pc1->
        exists type,type_glob_step type pc l fp pc1.
    Proof.
      intros.
      inversion H;subst.
      exists core;econstructor 1;eauto.
      exists call;econstructor 2;eauto.
      exists ret;econstructor 3;eauto.
      exists glob_halt;econstructor 4;eauto.
      exists entat;econstructor 5;eauto.
      exists extat;econstructor 6;eauto.
      exists efprint;econstructor 7;eauto.
      exists glob_sw;econstructor 8;eauto.
    Qed.
    Corollary type_glob_step_elim:
      forall t pc l fp pc1,
        type_glob_step t pc l fp pc1 -> @glob_step GE pc l fp pc1.
    Proof.
      intros;inversion H;subst;[econstructor 1|econstructor 2|econstructor 3|econstructor 4|econstructor 5|econstructor 6|econstructor 7|econstructor 8];eauto.
    Qed.

  Lemma core_step_equiv:
    forall pc fp pc',
      type_np_step core pc tau fp pc' <-> type_glob_step core pc tau fp pc'.
  Proof. split;intro; inversion H;econstructor;eauto. Qed.
  Lemma star_core_step_equiv:
    forall pc fp pc',
      tau_star (type_np_step core) pc fp pc' <->
      tau_star (type_glob_step core) pc fp pc'.
  Proof.
    split;intro;induction H;[constructor|econstructor 2 |constructor|econstructor 2];eauto; apply core_step_equiv;auto.
  Qed.
  Lemma call_step_equiv:
    forall pc fp pc',
      type_np_step call pc tau fp pc' <-> type_glob_step call pc tau fp pc'.
  Proof. split;intro;inversion H;econstructor 2;eauto. Qed.
  Lemma ret_step_equiv:
    forall pc fp pc',
      type_np_step ret pc tau fp pc' <-> type_glob_step ret pc tau fp pc'.
  Proof. split;intro;inversion H;econstructor 3;eauto. Qed.
  Lemma entat_step_equiv:
    forall pc fp pc',
      type_np_step entat pc tau fp pc' <-> type_glob_step entat pc tau fp pc'.
  Proof. split;intro;inversion H;subst;[econstructor 5|econstructor 6];eauto. Qed.
  Local Notation "{-| PC , T }" := 
    ({|thread_pool := thread_pool PC; cur_tid := T;gm := gm PC; atom_bit := atom_bit PC |})  (at level 70,right associativity).
  Lemma thrdhalt_step_equiv:
    forall pc pc',
      type_np_step thrdhalt pc sw FP.emp pc' <-> type_glob_step glob_halt pc tau FP.emp ({-|pc',cur_tid pc}) /\ type_glob_step glob_sw ({-|pc',cur_tid pc}) sw FP.emp pc'.
  Proof.
    intros;split;intro.
    inversion H;subst;simpl;split;econstructor;eauto.
    destruct H as [L1 L2];inversion L1;inversion L2;subst;simpl; econstructor;eauto.
  Qed.
  Lemma allhalt_step_equiv:
    forall pc pc',
      type_np_step allhalt pc tau FP.emp pc' <-> (type_glob_step glob_halt pc tau FP.emp pc' /\ (forall t,ThreadPool.valid_tid pc'.(thread_pool) t -> ThreadPool.halted pc'.(thread_pool) t)).
  Proof.
    intros;split;intro.
    inversion H;subst;split;auto;econstructor;eauto.
    inversion H;subst. inversion H0;subst;econstructor;eauto.
  Qed.
  Lemma extat_step_equiv:
    forall pc pc',
      type_np_step extat pc sw FP.emp pc' <-> type_glob_step extat pc tau FP.emp ({-|pc',cur_tid pc}) /\ type_glob_step glob_sw ({-|pc',cur_tid pc}) sw FP.emp pc'.
  Proof.
    intros;split;intro.
    inversion H;subst;simpl;split;econstructor;eauto.
    inversion H;inversion H0;inversion H1;subst;simpl;econstructor;eauto.
  Qed.
  Lemma efprint_step_equiv:
    forall pc x pc',
      type_np_step efprint pc (evt x) FP.emp pc' <-> type_glob_step efprint pc (evt x) FP.emp ({-|pc',cur_tid pc}) /\ type_glob_step glob_sw ({-|pc',cur_tid pc}) sw FP.emp pc'.
  Proof.
    intros;split;intro.
    inversion H;subst;simpl;split;econstructor;eauto.
    inversion H;subst;inversion H0;inversion H1;subst;econstructor;eauto.
  Qed.
 

  Lemma tau_star_np_step_star_glob_step:
    forall pc pc' fp',
      tau_star (@np_step GE) pc fp' pc' ->
      tau_star glob_step pc fp' pc'.
  Proof.
    intros.
    induction H.
    constructor.
    apply type_step_exists in H as [] .
    destruct x;try (inversion H;reflexivity).
    apply core_step_equiv in H;apply type_glob_step_elim in H;econstructor 2;eauto.
    apply call_step_equiv in H;apply type_glob_step_elim in H;econstructor 2;eauto.
    apply ret_step_equiv in H;apply type_glob_step_elim in H;econstructor 2;eauto.
    apply entat_step_equiv in H;apply type_glob_step_elim in H;econstructor 2;eauto.
    assert(L:fp=FP.emp). inversion H;auto. subst.
    apply allhalt_step_equiv in H as [];apply type_glob_step_elim in H;econstructor 2;eauto.
  Qed.

End typed_step.

Section local_glob_relation.
  Local Notation "'<<' i ',' c ',' sg ',' F '>>'" := {|Core.i := i; Core.c := c; Core.sg := sg; Core.F := F|} (at level 60, right associativity).
  Local Definition pc_valid_tid {ge}:= @GSimDefs.pc_valid_tid ge.
  Local Notation "{ A , B , C , D }" := {|thread_pool:=A;cur_tid:=B;gm:=C;atom_bit:= D|}(at level 70,right associativity).
  Local Notation "{-| PC , T }" := ({|thread_pool := thread_pool PC; cur_tid := T;gm := gm PC; atom_bit := atom_bit PC |}) (at level 70,right associativity).
  Variable GE:GlobEnv.t.
   
  Lemma localstep_corestep:
    forall  i_x F c m fp c' m',
      let: Mod := GlobEnv.modules GE i_x in
      let: lang := ModSem.lang Mod in
      let: Ge := ModSem.Ge Mod in
      let: fl := FLists.get_fl (GlobEnv.freelists GE) F in
      step lang Ge fl c m fp c' m' ->
      forall (tp: @ThreadPool.t GE) i sg b cs,
        ThreadPool.get_cs tp i = Some ((Core.Build_t i_x c sg F)::cs)  ->
        exists tp',
          type_glob_step core (Build_ProgConfig GE tp i m b) tau fp
                         (Build_ProgConfig GE tp' i m' b) /\
          ThreadPool.update tp i (Core.Build_t i_x c' sg F) tp'.
  Proof.
    intros.
    assert (exists tp', ThreadPool.update
                     tp i
                     {| Core.i := i_x; Core.c := c'; Core.sg:= sg; Core.F := F |} tp').
    {
      assert (exists cs',
                 CallStack.update
                   ({| Core.c := c; Core.sg:= sg; Core.F := F |}::cs)
                   {| Core.c := c'; Core.sg:= sg; Core.F := F |} cs').
      { eexists. econstructor; eauto.
        econstructor; eauto. }
      destruct H1 as (cs' & H_cs_upd).
      eexists; econstructor; eauto.
    }
    destruct H1 as (tp' & H_tp_upd).
    exists tp'. split. econstructor;eauto.
    unfold ThreadPool.get_top. rewrite H0. simpl. eauto.
    eauto.
    constructor;auto.
    auto.
  Qed.
  
  Lemma localplus_coreplus:
    forall i_x F c m fp c' m',
      let: Mod := GlobEnv.modules GE i_x in
      let: lang := ModSem.lang Mod in
      let: Ge := ModSem.Ge Mod in
      let: fl := FLists.get_fl (GlobEnv.freelists GE) F in
      plus (step lang Ge fl) c m fp c' m' ->
      forall (tp: @ThreadPool.t GE) i sg b cs,
        ThreadPool.get_cs tp i = Some (Core.Build_t i_x c sg F :: cs) ->
        exists tp',
          tau_plus (type_glob_step core) (Build_ProgConfig GE tp i m b) fp
                   (Build_ProgConfig GE tp' i m' b) /\
            ThreadPool.update tp i {| Core.c:=c'; Core.sg:=sg; Core.F:=F |} tp'.
  Proof.
    clear. intros i_x F c m fp c' m' H.
    induction H; intros.
    {
      eapply localstep_corestep with(b:=b) in H; eauto.
      destruct H as (tp'& Hstep & Htp'). eexists; split;[constructor|];eauto.
    }
    {
      eapply localstep_corestep in H; eauto.
      destruct H as (tp' & Hstep & Htp'). instantiate (1:=b) in Hstep.
      inversion Htp'.
      rewrite H1 in H. inversion H. 
      edestruct (IHplus tp' i sg b cs) as [tp'' [Hplus' Htp''] ].
      subst. unfold ThreadPool.get_cs; simpl.
      rewrite Maps.PMap.gsspec. destruct peq; [|congruence].
      inversion H2. auto.
      exists tp''. split. eapply tau_plus_cons; eauto.
      inversion Htp''. subst; simpl in *; clear Hplus' IHplus H0 Hstep Htp''.
      unfold ThreadPool.get_cs in H5; simpl in H5; rewrite Maps.PMap.gsspec in H5.
      destruct peq; [|congruence]. inversion H5; subst.
      repeat (econstructor; eauto).
      f_equal.
      inversion H7. rewrite Maps.PMap.set2. subst.
      inversion H2; auto.
    }
  Qed.
  
 
  Lemma localstar_corestar:
    forall i_x F c m fp c' m',
      let: Mod := GlobEnv.modules GE i_x in
      let: lang := ModSem.lang Mod in
      let: Ge := ModSem.Ge Mod in
      let: fl := FLists.get_fl (GlobEnv.freelists GE) F in
      InteractionSemantics.star (step lang Ge fl) c m fp c' m' ->
      forall (tp: @ThreadPool.t GE) i sg b cs,
        ThreadPool.get_cs tp i = Some ((Core.Build_t i_x c sg F)::cs) ->
        exists tp',
          tau_star (type_glob_step core) (Build_ProgConfig GE tp i m b) fp
                   (Build_ProgConfig GE tp' i m' b) /\
          (ThreadPool.update tp i (<< i_x, c', sg, F>>) tp' \/
           m = m' /\ c = c' /\ tp = tp' /\ fp = FP.emp).
  Proof.
    clear. intros i_x F c m fp c' m' H.
    destruct H; intros.
    {
      eexists; split; [econstructor|]; eauto.
    }
    {
      eapply step_star_plus in H0; eauto.
      eapply localplus_coreplus with(b:=b) in H0; eauto.
        destruct H0 as [tp' [Hplus Htp'] ].
        exists tp'. split; eauto.
        apply tau_plus2star. eauto.
    }
  Qed.
  
  Lemma corestep_localstep:
    forall thdp t gm d c fp thdp' gm',
      type_glob_step core ({thdp,t,gm,d}) tau fp ({thdp',t,gm',d}) ->
      ThreadPool.get_top thdp t = Some c  ->
      exists cc' c',
        step (ModSem.lang (GlobEnv.modules GE (Core.i c)))
             (ModSem.Ge (GlobEnv.modules GE (Core.i c)))
             (FLists.get_fl (GlobEnv.freelists GE) (Core.F c)) (Core.c c) gm fp cc' gm'/\
        Core.update c cc' c' /\
        ThreadPool.update thdp t c' thdp'.
  Proof.
    intros.
    inversion H;subst.
    pose proof H0 as Tmp1.
    rewrite H_tp_core in Tmp1.
    inversion Tmp1;clear Tmp1;subst.
    exists cc',c'.
    split;auto.
  Qed.

  Lemma coreplus_localplus:
    forall thdp t gm d fp thdp' gm',
      tau_plus (type_glob_step core) ({thdp,t,gm,d}) fp ({thdp',t,gm',d}) ->
      forall i_x c sg F,
        ThreadPool.get_top thdp t = Some (<<i_x,c,sg,F>>)  ->
        exists cc',
          InteractionSemantics.plus (step (ModSem.lang (GlobEnv.modules GE i_x))
                                          (ModSem.Ge (GlobEnv.modules GE i_x))
                                          (FLists.get_fl (GlobEnv.freelists GE) F)) c gm fp cc' gm' /\
          ThreadPool.update thdp t (<<i_x,cc',sg,F >>) thdp'.
  Proof.
    intros until gm'.
    intro H.
    apply tau_plus_tau_N_equiv in H as [].
    revert H.
    revert thdp t gm d fp thdp'.
    induction x;intros.
    inversion H;clear H;subst.
    inversion H3;clear H3;subst.
    rewrite FP.fp_union_emp.
    eapply corestep_localstep in H2;eauto.
    destruct H2 as (cc'&c'&step&core_upd&thpd_upd).
    exists cc'.
    split.
    constructor;auto.
    inversion core_upd;subst;auto.
    
    inversion H;clear H;subst.
    destruct s'.
    assert(cur_tid = t /\ atom_bit =d).
    inversion H2;subst;auto.
    destruct H;subst.
    eapply corestep_localstep in H2;eauto.
    destruct H2 as (cc1&c1&step1&core_upd&thdp_upd).
    assert(ThreadPool.get_top thread_pool t = Some c1).
    inversion thdp_upd;subst.
    unfold ThreadPool.get_top.
    unfold ThreadPool.get_cs.
    simpl.
    rewrite Maps.PMap.gsspec.
    destruct peq;try contradiction.
    inversion H1;subst;auto.
    
    inversion core_upd;subst.
    simpl in *.
    eapply IHx in H as (cc'&coreplus&thdp_upd2);eauto.
    exists cc'.
    split. econstructor 2;eauto.
    
    inversion thdp_upd;subst.
    inversion H1;subst.
    unfold ThreadPool.get_top in H0.
    rewrite H in H0.
    inversion H0;subst.
    
    inversion thdp_upd2;subst.
    unfold ThreadPool.get_cs in H4.
    simpl in *.
    rewrite Maps.PMap.gsspec in H4.
    destruct peq;[|contradiction].
    inversion H4;clear H4;subst.
    rewrite Maps.PMap.set2.
    inversion H5;subst.
    repeat (econstructor;eauto).
  Qed.
  
  Lemma corestar_localstar:
    forall thdp t gm d fp thdp' gm',
      tau_star (type_glob_step core) ({thdp,t,gm,d}) fp ({thdp',t,gm',d}) ->
      forall i_x c sg F,
        ThreadPool.get_top thdp t = Some (<<i_x,c,sg,F>>)  ->
        exists cc',
          InteractionSemantics.star (step (ModSem.lang (GlobEnv.modules GE i_x))
                                          (ModSem.Ge (GlobEnv.modules GE i_x))
                                          (FLists.get_fl (GlobEnv.freelists GE) F)) c gm fp cc' gm' /\
          ( ThreadPool.update thdp t (<<i_x,cc',sg,F >>) thdp' \/ fp=FP.emp /\ thdp = thdp' /\ gm = gm' ).
  Proof.
    intros.
    apply tau_star_tau_N_equiv in H as [].
    destruct x.
    inversion H;subst.
    exists c.
    split;[constructor|];auto.
    
    assert(exists x,tau_N (type_glob_step core) (S x) ({thdp, t, gm, d}) fp ({thdp', t, gm', d})). eauto.
    apply tau_plus_tau_N_equiv in H1.
    eapply coreplus_localplus in H1;eauto.
    destruct H1 as (cc'&plus'&upd).
    exists cc'.
    split;auto.
    revert plus'.
    clear.
    intro.
    induction plus'.
    rewrite <- FP.fp_union_emp with(fp:=fp).
    econstructor 2;eauto;econstructor.
    econstructor 2;eauto.
  Qed.
  Lemma local_core_step:
    forall GE thdp t gm fp c cc' gm',
      ThreadPool.get_top thdp t = Some c ->
      step (ModSem.lang (GlobEnv.modules GE (Core.i c)))
           (ModSem.Ge (GlobEnv.modules GE (Core.i c)))
           (FLists.get_fl (GlobEnv.freelists GE) (Core.F c)) 
           (Core.c c) gm fp cc' gm' ->
      exists c',Core.update c cc' c' /\ exists thdp',  ThreadPool.update thdp t c' thdp'.
  Proof.
    intros until gm'.
    intros H_tp_core H_core_step.
    assert(exists c',Core.update c cc' c').
    eexists;econstructor;eauto.
    destruct H as (c'&H_core_upd).
    pose proof H_tp_core as backup1.
    unfold ThreadPool.get_top in H_tp_core.
    destruct (ThreadPool.get_cs thdp t) eqn:eq;[|inversion H_tp_core].
    unfold CallStack.top in H_tp_core.
    destruct t0 eqn:eq2;inversion H_tp_core;subst;clear H_tp_core.
    rename backup1 into H_tp_core.
    assert(exists thdp',ThreadPool.update thdp t c' thdp').
    eexists. econstructor;eauto. econstructor;eauto.
    destruct H as (t'&H_tp_upd).
    econstructor;econstructor;eauto.
  Qed.
  Lemma star_local_core_step:
    forall GE i_x F c gm fp c' gm',
      InteractionSemantics.star (step (ModSem.lang (GlobEnv.modules GE i_x)) (ModSem.Ge (GlobEnv.modules GE i_x))(FLists.get_fl (GlobEnv.freelists GE) F)) c gm fp c' gm' ->
      forall thdp t sg d,
       ThreadPool.get_top thdp t = Some ({| Core.i := i_x; Core.c := c; Core.sg := sg; Core.F := F |}) ->
       exists thdp' : ThreadPool.t,
         tau_star (type_glob_step core) ({thdp, t, gm, d}) fp ({thdp', t, gm', d}).
  Proof.
    intros until gm'.
    intro H.
    induction H;intros.
    exists thdp. constructor.

    pose proof H1 as Tmp1.
    eapply local_core_step in Tmp1 as (c1&?&thdp1&?);eauto.
    assert(type_glob_step core ({thdp,t,m,d}) tau fp ({thdp1,t,m',d})).
    econstructor;eauto.
    inversion H2;subst.
    inversion H3;subst.
    simpl in *.
    inversion H6;subst.
    remember ({| Core.i := i_x; Core.c := c'; Core.sg := sg; Core.F := F |}) as c1.
    remember ( {|ThreadPool.content := Maps.PMap.set t (Some (c1 :: cs0)%list) (ThreadPool.content thdp); ThreadPool.next_tid := ThreadPool.next_tid thdp; ThreadPool.next_fmap := ThreadPool.next_fmap thdp |}) as thdp1.
    assert(ThreadPool.get_cs thdp1 t = Some (c1::cs0)%list).
    unfold ThreadPool.get_cs. rewrite Heqthdp1. simpl.
    rewrite Maps.PMap.gsspec.
    destruct Coqlib.peq;[auto|contradiction].
    assert(ThreadPool.get_top thdp1 t = Some c1).
    unfold ThreadPool.get_top.
    rewrite H8;auto.
    rewrite Heqc1 in H9.
    apply IHstar with(d:=d) in H9 as [thdp'].
    exists thdp'.
    rewrite Heqthdp1 in H9.
    econstructor 2;eauto.
  Qed.

  Lemma star_core_local:
    forall ge pc fp pc',
      tau_star (@type_glob_step ge core) pc fp pc' ->
      forall c ,
        ThreadPool.get_top pc.(thread_pool) pc.(cur_tid) = Some c ->
        exists c',
        InteractionSemantics.star (step (ModSem.lang (GlobEnv.modules ge (Core.i c))) (ModSem.Ge (GlobEnv.modules ge (Core.i c)))(FLists.get_fl (GlobEnv.freelists ge) (Core.F c))) (Core.c c) pc.(gm) fp c' pc'.(gm).
  Proof.
    intros until pc'.
    intro.
    induction H;intros.
    eexists. constructor.
    inversion H;subst.
    simpl in *.
    rewrite H_tp_core in H1;inversion H1;clear H1;subst.
    inversion H_core_upd;subst.
    assert(ThreadPool.get_top thdp' t = Some (<<Core.i c,cc',Core.sg c,Core.F c>>)).
    inversion H_tp_upd;subst.
    unfold ThreadPool.get_top;unfold ThreadPool.get_cs;simpl.
    rewrite Maps.PMap.gsspec. destruct Coqlib.peq;[|contradiction].
    inversion H2;subst;auto.
    apply IHtau_star in H1 as [].
    simpl in H1.
    eexists. econstructor 2;eauto.
  Qed.
    


  End local_glob_relation.