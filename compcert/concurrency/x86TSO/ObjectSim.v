(** This file gives the definition of [object simulation] and 
[RespectPerm (Io, Ro, Go)] *)
Require Import Coqlib Maps Axioms.     
Require Import AST Integers Floats Values Events Globalenvs Smallstep.

Require Import CUAST.

Require Import Footprint GMemory TSOMem MemAux.
Require Import GlobDefs GAST ETrace.

Require Import ASM_local AsmLang AsmTSO TSOGlobSem.
Require Import InteractionSemantics.
Require Import RGRels FMemory ClientSim.

(** * Object module simulation *)
Section ObjectSim.

  Variable Ro: genv -> tid -> stRel.
  Variable Go: genv -> tid -> stRel.
  Variable Io: genv -> stInv.

  (** List the properties of object simulation: *)
  Record objectsim_properties
         {sl: Language}
         (sge: Genv.t (F sl) (V sl))
         (sG: G sl)
         (tge: genv)
         (match_state: tid -> (core sl * gmem) -> (AsmTSO.core * tsomem) -> Prop): Prop :=
    {
      (** The initial state satisfies the object invariant [Io] *)
      match_initmem:
        forall sm gm tm,
          init_gmem sl sge sm ->
          AsmTSO.init_gmem tge gm ->
          tm = tsomem_init gm ->
          Io tge sm tm
      ;

      (** If the initial state satisfies [Io], then it satifies the match_state *)
      match_init:
         forall id args tc,
           AsmTSO.init_core tge id args = Some tc ->
           exists sc,
             init_core sl sG id args = Some sc /\
             (forall t sm tm,
                 Io tge sm tm ->
                 match_state t (sc, sm) (tc, tm))
      ;

      match_init_none:
        forall id args,
          AsmTSO.init_core tge id args = None ->
          init_core sl sG id args = None
      ;

      (** If the states of low- and high-level program satisfy [match_state] and 
          the low-level program can execute a step, we can know that the high-level 
          program can execute star steps and their program states still satisfy 
          the [match_state], or the high-level program aborts after star steps.
      *)
      match_tau:
        forall t sc sm tc tm b gm fl fp tc' b' gm',
          match_state t (sc, sm) (tc, tm) ->
          tso_buffers tm t = b ->
          memory tm = gm ->
          tm_alloc_not_fl tm fl t -> rel_tm_gm_vb sm tm fl t ->
          tsostep tge fl tc (b, gm) fp tc' (b', gm') ->
          let tm' := (mktsomem (tupdate t b' (tso_buffers tm)) gm') in
          (* normal star step *)
          (exists FP sc' sm',
              star (step sl sG fl) sc sm FP sc' sm' /\
              (
                (* match after star step *)
                ( Go tge t sm tm sm' tm' /\
                  match_state t (sc', sm') (tc', tm') /\
                  tm_alloc_not_fl tm' fl t /\
                  rel_tm_gm_vb sm' tm' fl t /\
                  obj_fp sm sm' fp
                )
                \/
                (* abort after star step *)
                ((forall FP' sc'' sm'', ~ step sl sG fl sc' sm' FP' sc'' sm'')
                 /\ at_external sl sG sc' = None
                 /\ (forall ores, after_external sl sc' ores = None)
                 /\ halt sl sc' = None)
                  
              )
          )
          \/
          (* atomic block *)
          (exists FP1 sc_ent sm1 sc_ent' FP2 sc_ext sm' sc',
              (* star step *)
              star (step sl sG fl) sc sm FP1 sc_ent sm1 /\
              (* ent atom *)
              at_external sl sG sc_ent = Some (ent_atom, ent_atom_sg, nil) /\
              after_external sl sc_ent None = Some sc_ent' /\
              (* star step *)
              star (step sl sG fl) sc_ent' sm1 FP2 sc_ext sm' /\
              
              (
                ( (* ext atom and match *)
                  at_external sl sG sc_ext = Some (ext_atom, ext_atom_sg, nil) /\
                  after_external sl sc_ext None = Some sc' /\
                  Go tge t sm tm sm' tm' /\
                  match_state t (sc', sm') (tc', tm') /\
                  tm_alloc_not_fl tm' fl t /\
                  rel_tm_gm_vb sm' tm' fl t /\
                  obj_fp sm sm' fp
                )
                \/
                ( (* abort inside atomic block *)
                  (forall FP' sc' sm'', ~ step sl sG fl sc_ext sm' FP' sc' sm'')
                  /\ at_external sl sG sc_ext = None
                  /\ (forall ores, after_external sl sc_ext ores = None)
                  /\ halt sl sc_ext = None
                )
              )
          )
      ;

      (** unbuffer_safe holds in the execution of object code *)
      match_tau_unbuffer_safe:
         forall t sc sm tc tm,
           match_state t (sc, sm) (tc, tm) ->
           unbuffer_safe tm
      ;

      (** The footprint caused by object are restricted in the object memory, 
         or a block new allocated
      *)
      match_tau_obj_mem_fp:
         forall t sc sm tc tm b gm fl fp tc' b' gm',
           match_state t (sc, sm) (tc, tm) ->
           tso_buffers tm t = b ->
           memory tm = gm ->
           tsostep tge fl tc (b, gm) fp tc' (b', gm') ->
           (forall b ofs,
               Locs.belongsto (FP.locs fp) b ofs ->
               (obj_mem sm b ofs \/ (exists n, get_block fl n = b)))
      ;
      
      (** object would not call external function *)
      match_no_extcall:
        forall t sc sm tc tm,
          match_state t (sc, sm) (tc, tm) ->
          AsmTSO.at_external tge tc = None
      ;

      match_halt:
        forall t sc sm tc tm rv,
          match_state t (sc, sm) (tc, tm) ->
          AsmTSO.halt tc = Some rv ->
          halt sl sc = Some rv
      ;

      match_halt_noscstep:
        forall t sc sm tc tm rv,
          match_state t (sc, sm) (tc, tm) ->
          AsmTSO.halt tc = Some rv ->
          (forall fl fp sc' sm', ~ step sl sG fl sc sm fp sc' sm')
          /\ at_external sl sG sc = None
      ;

      match_halt_none:
        forall t sc sm tc tm,
          match_state t (sc, sm) (tc, tm) ->
          AsmTSO.halt tc = None ->
          halt sl sc = None
      ;

      match_rely:
         forall t sc sm tc tm sm' tm',
          match_state t (sc, sm) (tc, tm) ->
          Ro tge t sm tm sm' tm' ->
          match_state t (sc, sm') (tc, tm')
      ;

      match_abort:
        forall t sc sm tc tm fl gm,
          match_state t (sc, sm) (tc, tm) ->
          tso_buffers tm t = nil ->
          memory tm = gm ->
          (forall fp tc' b' gm', ~ tsostep tge fl tc (nil, gm) fp tc' (b', gm')) ->
          AsmTSO.halt tc = None ->
          (forall fm, ~ FMemory.embed gm fl fm)
      ;
          
    }.
  
End ObjectSim.

(** The definition of object module simulation, which is corresponding to 
the [Definition 28] on page 17 in submission #115 supplemental text *)
Definition objectsim
           (Ro Go: genv -> tid -> stRel) (Io: genv -> stInv)
           (sl: Language)
           (scu: comp_unit sl)
           (tcu: AsmTSO.comp_unit) : Prop :=
  forall sge sG tge,
    init_genv sl scu sge sG ->
    AsmTSO.init_genv tcu tge ->
    genv_match _ _ sge tge ->
    exists match_state,
      objectsim_properties Ro Go Io sge sG tge match_state.



Definition loc_stable (m m' : gmem) (b : block) (ofs : Z) :=
  ZMap.get ofs ((GMem.mem_contents m) !! b) =
  ZMap.get ofs ((GMem.mem_contents m') !! b) /\
  (GMem.mem_access m) !! b ofs = (GMem.mem_access m') !! b ofs.

Definition buffer_item_insert (t : tid) (B : buffers) (bi : buffer_item) :=
  (tupdate t (B t ++ bi :: nil) B).

Definition tm_item_insert (t : tid) (tm : tsomem) (bi : buffer_item) :=
  mktsomem (buffer_item_insert t (tso_buffers tm) bi) (memory tm).

Definition env_unbuffer_step (t : tid) (tm tm' : tsomem) (M M' : gmem) :=
  unbuffer tm t = Some tm' /\ M = M'.

Definition env_inbuffer_step (t : tid) (M M' : gmem) (tm tm' : tsomem) :=
  memory tm = memory tm' /\
  (exists bis,
      tso_buffers tm' = tupdate t (tso_buffers tm t ++ bis) (tso_buffers tm) /\
      (forall (b : block) (ofs : Z),
          in_buffer bis b ofs -> ~ obj_mem M b ofs)) /\
  unbuffer_safe tm'.

Definition env_update_tm_step (t : tid) (M : gmem) (tm tm' : tsomem) :=
  tso_buffers tm = tso_buffers tm' /\
  (forall b ofs, obj_mem M b ofs -> loc_stable (memory tm) (memory tm') b ofs) /\
  unbuffer_safe tm'.

Definition env_m_stable (M M' : gmem) (tm tm' : tsomem) :=
  forall b ofs, ~ obj_mem M b ofs -> In b (GMem.validblocks M) ->
           (loc_stable M M' b ofs /\ loc_stable (memory tm) (memory tm') b ofs).

Definition obj_tau (M M' : gmem) (tm tm' : tsomem) :=
  GMem.validblocks M = GMem.validblocks M' /\
  tso_buffers tm = tso_buffers tm'.

Definition obj_alloc_b (t : tid) (M M' : gmem) (tm tm' : tsomem) :=
  exists b, ~ In b (GMem.validblocks M) /\
       (exists lo hi, tupdate t (tso_buffers tm t ++ (BufferedAlloc b lo hi) :: nil)
                         (tso_buffers tm) = tso_buffers tm' /\
                 Some M' = alloc M b lo hi) /\
       (forall t',  ~ (exists ofs, in_buffer (tso_buffers tm t') b ofs))
       /\ ~ In b (GMem.validblocks (memory tm)).

Definition obj_upd_objm (t : tid) (M M' : gmem) (tm tm' : tsomem) :=
  exists b ofs n, (forall l, (ofs <= l < ofs + size_chunk Mint32)%Z -> obj_mem M b l) /\
             tupdate t (tso_buffers tm t ++
                                    (BufferedStore Mint32 b ofs (Vint n)) :: nil)
                     (tso_buffers tm) = tso_buffers tm' /\
             GMem.validblocks M = GMem.validblocks M'
             (*/\
             (forall t', t <> t' ->
                         ~ (exists ofs, in_buffer (tso_buffers tm t') b ofs))*).

Definition env_not_touch_objm (M M' : gmem) (tm tm' : tsomem) :=
  (forall b ofs, obj_mem M b ofs -> eq_on_loc b ofs M M') /\
  (exists t, unbuffer tm t = Some tm' \/
        env_inbuffer_step t M M' tm tm') /\
  GMem.forward M M'.

(** * Respect Permission *)
(** The definition of [RespectPerm (Io, Ro, Go)] corresponds to the [Definition 27] 
(Respect permission) in submission #115 supplemental text. The Coq implementation 
includes more detail, because we omit some operations like `allocation` on paper 
and the memory model used for Coq proof is more complex. 
 *)
Record RespectPerm (Io : genv -> stInv)
       (Ro : genv -> tid -> stRel)
       (Go : genv -> tid -> stRel) : Prop :=
  Build_RespectPerm
    {
      Rp :
        forall M M' tm tm' ge t,
          Io ge M tm ->
          (** The object memory will not be modified *)
          (forall b ofs, obj_mem M b ofs -> loc_stable M M' b ofs) ->
          (exists t', t <> t' /\ GMem.forward M M' /\
                 (
                   (** unbuffer step *)
                   env_unbuffer_step t' tm tm' M M' \/
                   (** in buffer step *)
                   env_inbuffer_step t' M M' tm tm'
                 )
          ) -> Ro ge t M tm M' tm';

      Gp :
        forall M M' tm tm' ge t,
          Go ge t M tm M' tm' ->
          (env_m_stable M M' tm tm' /\ unbuffer_safe tm /\ unbuffer_safe tm' /\
           (** [obj_tau], [obj_alloc_b] and [obj_upd_objm] describe the state transistion that may be caused by the execution of object code *)
           (obj_tau M M' tm tm' \/
            obj_alloc_b t M M' tm tm' \/ obj_upd_objm t M M' tm tm') /\
           GMem.validblocks (memory tm) = GMem.validblocks (memory tm') /\
           GMem.mem_access (memory tm) = GMem.mem_access (memory tm') /\
           (forall b ofs, obj_mem M b ofs -> obj_mem M' b ofs) /\
           (forall b, ~ In b (GMem.validblocks M') ->
                 (forall ofs, ZMap.get ofs (GMem.mem_contents M) !! b =
                         ZMap.get ofs (GMem.mem_contents M') !! b)) /\
           (forall b, ~ In b (GMem.validblocks (memory tm')) ->
                 (forall ofs, ZMap.get ofs (GMem.mem_contents (memory tm)) !! b =
                         ZMap.get ofs (GMem.mem_contents (memory tm')) !! b)));
      Ip :
        forall M M' tm tm' ge,
          Io ge M tm ->
          env_not_touch_objm M M' tm tm' ->
          Io ge M' tm'
    }.
