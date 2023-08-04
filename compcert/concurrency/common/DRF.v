Require Import Footprint GMemory InteractionSemantics GAST GlobDefs GlobSemantics Blockset.

(** * Data Race Freedom *)

(** This file defines data-race-free property of whole proram. 
    Intuitively, it says at each program point, the next step
    of any two threads would not have conflicting footprint.
    Conflict means accessing the same memory location, 
    and one of the accesses is write.
 *)


(** [predict] is used in the definition of data-race, in Fig.9 of the paper.
When the bit is O, we make an one-step prediction outside atomic block, which is exactly the case of [predict-O] in Fig.9. Otherwise the bit is I, and we make a multiple-step prediction entering atomic block and executing inside the atomic block, which is [predict-I] in Fig.9.
*)
Inductive predict {GE: GlobEnv.t}: @ProgConfig GE -> tid -> Bit -> FP.t -> Prop :=
| predict0:
    forall thdp t gm t' c cc' gm' fp,
      let: cc := Core.c c in
      let: c_ix := Core.i c in
      let: c_f := Core.F c in
      let: c_fl := FLists.get_fl (GlobEnv.freelists GE) c_f in
      let: c_mod := GlobEnv.modules GE c_ix in
      let: c_lang := ModSem.lang c_mod in
      let: Ge := ModSem.Ge c_mod in
      forall
        (H_tp_core: ThreadPool.get_top thdp t' = Some c)
        (H_core_step: step c_lang Ge c_fl cc gm fp cc' gm'),
        (* ===================================================== *)
        predict (Build_ProgConfig GE thdp t gm O) t' O fp
              
| predict1:
    forall thdp t gm t' c cc' cc'' gm' fp,
      let: cc := Core.c c in
      let: c_ix := Core.i c in
      let: c_f := Core.F c in
      let: c_fl := FLists.get_fl (GlobEnv.freelists GE) c_f in
      let: c_mod := GlobEnv.modules GE c_ix in
      let: c_lang := ModSem.lang c_mod in
      let: Ge := ModSem.Ge c_mod in
      forall
        (H_tp_core: ThreadPool.get_top thdp t' = Some c)
        (H_core_atext: at_external c_lang Ge cc = Some (ent_atom, ent_atom_sg, nil))
        (H_core_aftext: after_external c_lang cc None = Some cc')
        (H_core_step: star (step c_lang Ge c_fl) cc' gm fp cc'' gm'),
        (* ===================================================== *)
        predict (Build_ProgConfig GE thdp t gm O) t' I fp.

(** The definition of data-race, the same as the [Race] rule in Fig.9.
Configuration S is racy if two different threads of S are predicted to generated conflicting footprints and at least one thread is not predicted inside atomic block.
*)
Inductive race_config {ge: GlobEnv.t} : @ProgConfig ge -> Prop :=
  Race_config: forall s t1 b1 fp1 t2 b2 fp2,
    t1 <> t2 ->
    predict s t1 b1 fp1 ->
    predict s t2 b2 fp2 ->
    b1 <> I \/ b2 <> I ->
    FP.conflict fp1 fp2 ->
    @race_config ge s.

(** A will-race configuration is a configuration that will be predicted to have a data-race after several steps of execution.
 *)
Definition star_race_config {ge}(pc:@ProgConfig ge):Prop:=
  exists l fp pc',ETrace.star glob_step  pc l fp pc' /\ race_config pc'.

(** The program is racy if it can be loaded into a configuration that will race.*)
Definition race_prog {NL}{L:@langs NL}(p:prog L):Prop:=
  exists gm ge pc t,init_config p gm ge pc t /\ star_race_config pc.

(** The program is data-race-free if it is not racy.*)
Definition drf {NL} {L} p : Prop := ~ @race_prog NL L p.
