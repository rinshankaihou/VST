Require Import Setoid List.
Require Import Coqlib Errors Values AST Globalenvs.
Require Import Memory Footprint InteractionSemantics.


Record sem_local :=
  {
    F: Type;
    V: Type;
    G: Type;
    comp_unit: Type;
    core: Type;
    
    (* init_genv_local: comp_unit L -> Genv.t (F L) (V L) -> (G L) -> Prop; *)
    init_genv_local: comp_unit -> Genv.t F V -> G -> Prop;
    (* init_mem: Genv.t (F L) (V L) -> mem -> Prop; *)
    (** TODO: is init_mem relative to languages, since we already have Genv.t definition *)
    init_mem: Genv.t F V -> mem -> Prop;

    (*
    init_core_local: (G L) -> ident -> list val -> option (core L);
    (** Note: here we require halt returns a value with its type *)
    (** EDIT: this is not viable. CompCert languages won't expose type information at callstate *)
    halt_local: (core L) -> option val;
    step_local: (G L) -> (core L) -> mem -> FP.t -> (core L) -> mem -> Prop;
    (** EDIT: since external function is defined as a (name: string) with its signature,
        here we modify at_external interface to adapt string name, by providing global environment  *)
    at_external_local: (G L) -> (core L) -> option (ident * signature * list val);
    after_external_local: (core L) -> option val -> option (core L);
     *)
    
    init_core_local: G -> ident -> list val -> option core;
    (** Note: here we require halt returns a value with its type *)
    (** EDIT: this is not viable. CompCert languages won't expose type information at callstate *)
    halt_local: core -> option val;
    step_local: G -> core -> mem -> FP.t -> core -> mem -> Prop;
    (** EDIT: since external function is defined as a (name: string) with its signature,
        here we modify at_external interface to adapt string name, by providing global environment  *)
    at_external_local: G -> core -> option (ident * signature * list val);
    after_external_local: core -> option val -> option core;
  }.