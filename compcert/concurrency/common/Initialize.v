Require Import Axioms Coqlib Errors Maps AST Globalenvs Integers Floats Values.

Require Import GMemory MemAux InteractionSemantics GlobDefs GlobSemantics.

(** This file we define initial program configurations *)

(** The initializer for global environments will check if there is a globvar defined twice,
    and if the [readonly], [volatile] fields of global variables matches. 
    For function definitions, we use [internal_fn] interface, 
    and check if the internal function names conflict, so that we never redefine a function.
 *)

(** [TODO] How did C standard define the behavior when two files has conflicting function name? 
    Seems that the linker would throw an error message..
 *)

(** [TODO] How did CompCert deal with [extern] keyword, is the variable declared with [extern] has 
    an initial data in AST? 
    According to testing result on [clightgen]:
    1. The [extern] variables has no init_data, i.e. the [gvar_init] field is [nil];
    2. [alloc_global] would allocate a memory block is size of 0 for [extern] vars;
    
    [Question]: can we define a global variable with empty init_data, thus has the same form as [extern]s?
    In this way, it seems a erroneous module linked another module could make it safe, e.g.
    
    MOD A:
    declare int x as global with nil init_data;
    void main(){
      x = 1;  
    }
    
    MOD B:
    int x;

 *)

(** [TODO] Then what about [static]?
    Could address of static global variable leaked to public global variables? 
    Will CompCert do optimizations assuming static global variables are not modified by environment? 

    According to testing result on [clightgen]:
    1. when a module import an [extern] variable with conflicting name with a [static] variable,
    CompCert uses the static one in the module.
    
    According to external function properties, external function could modify static variables
    only if the static variable is reachable from public global variables _at_ the call point.
 *)

(** [TODO] What kind of symbols are not public (A: [static])? 
    How to deal with these symbols when generating [genv]? (A: add to [ge] but not [ge_public])
 *)


Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.

Local Open Scope pair_scope.

(** * Global Environment *)
(** We modify the [globalenv] interface since we need linking modules *)

(** ** Constructing the global environment *)
Print globdef.
Print program.
Print Language.

Section ModGlobEnv.
Variable F V: Type.

(** We use an auxiliary [ge_public] to record public idents and its corresponding block/definition *)

Variable ge_public: Genv.t unit unit.
Variable fn_defined: list ident.
(** there is an invariant that idents in [fn_defined] are in domain of ge_public. *)
Hypothesis defined_in_domain: forall id, In id fn_defined ->
                                    exists b, Genv.find_symbol ge_public id = Some b /\
                                         Genv.find_def ge_public b = Some (Gfun tt).


(** [mod_add_global] takes 4 arguments:
    1. A "global" globenv, recording all global idents already added for all modules
    2. A list of ident, recording all functions that is _defined_ by previous modules
    3. The target global environment to be added with the 4th argument
    4. A pair of ident and global definition
    
    if a globdef is already defined else where, then the process aborts *)

(** First we check if an ident is public and used before, if not, it could be safely added to globenv *)
Definition non_conflicting_symbol (ge: Genv.t F V) (id: ident) : bool :=
  if Genv.public_symbol ge id
  then
    match Genv.find_symbol ge_public id with
    | Some _ => true
    | None => false
    end
  else true.

Definition strip_globdef (gd: globdef F V) : globdef unit unit :=
  match gd with
  | Gfun _ => Gfun tt
  | Gvar gvar =>
    Gvar {| gvar_info := tt;
            gvar_init := gvar_init gvar;
            gvar_readonly := gvar_readonly gvar;
            gvar_volatile := gvar_volatile gvar |}
  end.

Program Definition mod_add_global_fresh (ge: Genv.t F V) (idg: ident * globdef F V) : Genv.t F V :=
  @Genv.mkgenv F V
    (Genv.genv_public ge)
    (PTree.set idg#1 ge.(Genv.genv_next) ge.(Genv.genv_symb))
    (PTree.set ge.(Genv.genv_next) idg#2 ge.(Genv.genv_defs))
    (Psucc ge.(Genv.genv_next))
    _ _ _.
Next Obligation.
  destruct ge; simpl in *.
  rewrite PTree.gsspec in H. destruct (peq id i). inv H. apply Plt_succ.
  apply Plt_trans_succ; eauto.
Qed.
Next Obligation.
  destruct ge; simpl in *.
  rewrite PTree.gsspec in H. destruct (peq b genv_next).
  inv H. apply Plt_succ.
  apply Plt_trans_succ; eauto.
Qed.
Next Obligation.
  destruct ge; simpl in *.
  rewrite PTree.gsspec in H. rewrite PTree.gsspec in H0.
  destruct (peq id1 i); destruct (peq id2 i).
  congruence.
  inv H. eelim Plt_strict. eapply genv_symb_range; eauto.
  inv H0. eelim Plt_strict. eapply genv_symb_range; eauto.
  eauto.
Qed.

Program Definition mod_add_global_old (ge: Genv.t F V) (idg: ident * globdef F V)
        (b: block) (H_blt: Plt b (Genv.genv_next ge))
        (H_bfresh: Genv.invert_symbol ge b = None): Genv.t F V :=
  @Genv.mkgenv F V
    (Genv.genv_public ge)
    (PTree.set idg#1 b ge.(Genv.genv_symb))
    (PTree.set b idg#2 ge.(Genv.genv_defs))
    (Psucc ge.(Genv.genv_next))
    _ _ _.
Next Obligation.
  destruct ge; simpl in *.
  rewrite PTree.gsspec in H. destruct (peq id i).
  inv H. apply Plt_trans_succ; eauto. 
  apply Plt_trans_succ; eauto.
Qed.
Next Obligation.
  destruct ge; simpl in *.
  rewrite PTree.gsspec in H. destruct (peq b0 b).
  inv H. apply Plt_trans_succ; eauto.
  apply Plt_trans_succ; eauto.
Qed.
Next Obligation.
  destruct ge eqn:Hge; simpl in *.
  rewrite PTree.gsspec in H. rewrite PTree.gsspec in H0.
  destruct (peq id1 i); destruct (peq id2 i).
  congruence.
  exploit (Genv.find_invert_symbol ge id2); eauto. inv H. eauto.
  intro. congruence.
  exploit (Genv.find_invert_symbol ge id1); eauto. inv H. eauto.
  intro. congruence.
  eauto.
Qed.
  

(** If the ident is declared previously, we should be careful and see if it is actually _defined_.
    We do this by first get the global definition and see if it is a Gfun or Gvar. 
    Only when glob_defs has the same type (fun/var), 
    and the globvar in [ge_glob] is less defined than, or the globfun in [ge_glob] is compatible with
    that is in [idg], could this glob def added to [ge_glob] and [ge], and reuse the previous block.
 *)
Definition gfun_defined (gfunl: list ident) (id: ident) := in_dec ident_eq id gfunl.

Definition gvar_defined {V': Type} (gvar: globvar V') : bool :=
  match gvar_init gvar with
  | nil => false
  | _ :: _ => true
  end.

Definition compatible (id: ident)
           (gd0: globdef unit unit) (fn_defined: list ident)
           (gd: globdef F V) (internal_fn: list ident) : bool :=
  match gd0, gd with
  | Gfun _, Gfun _ =>
    match gfun_defined fn_defined id, gfun_defined internal_fn id with
    | true, true => false
    | _, _ => true
    end
  | Gvar gvar0, Gvar gvar =>
    match gvar_defined gvar0, gvar_defined gvar with
    | true, true => false
    | 
    
    

Definition get_globdef (ge_glob: Genv.t unit unit) (id: ident) : option (block * globdef unit unit) :=
  match Genv.find_symbol ge_glob id with
  | None => None
  | Some b =>
    match Genv.find_def ge_glob b with
    | None => None
    | Some gd => Some (b, gd)
    end
  end.


(** for functions, we record the internal function idents in a list and simply look up that list *)


(** for global vars, we search in [ge_glob], a Genv.t recording previously generated environments *)


Definition gvar_declared (ge_glob: Genv.t unit unit) (id: ident) : option (block * bool * bool) :=
  match get_globdef ge_glob id with
  | Some (b, gd) =>
    match gd with
    | Gvar gvar =>
      match gvar_init gvar with
      | nil => Some (b, gvar_readonly gvar, gvar_volatile gvar)
      | _ :: _ => None
      end
    | _ => None
    end
  | None => None
  end.

Program Definition mod_add_global
        (ge_glob: Genv.t unit unit) (fn_defined: list ident)
        (ge: Genv.t F V) (internal_fn: list ident)
        (idg: ident * globdef F V) :
  Genv.t unit unit * list ident * Genv.t F V * list ident :=
  
 
  
Definition gvar_defined (ge_glob: Genv.t unit unit) (idg: ident * globaldef F V) : bool :=
  match idg with
  | (id, gdef) =>
    match find_symbol id with
    | None => false
    | Some b =>
      match find_def b with
      (* what if find_def cannot find the definition? *)
      (* wierd... *)
      | None => false
      | 
    
                           


Program Definition add_global (ge: t) (idg: ident * globdef F V) : t :=
  @mkgenv
    ge.(genv_public)
    (PTree.set idg#1 ge.(genv_next) ge.(genv_symb))
    (PTree.set ge.(genv_next) idg#2 ge.(genv_defs))
    (Psucc ge.(genv_next))
    _ _ _.
Next Obligation.
  destruct ge; simpl in *.
  rewrite PTree.gsspec in H. destruct (peq id i). inv H. apply Plt_succ.
  apply Plt_trans_succ; eauto.
Qed.
Next Obligation.
  destruct ge; simpl in *.
  rewrite PTree.gsspec in H. destruct (peq b genv_next0).
  inv H. apply Plt_succ.
  apply Plt_trans_succ; eauto.
Qed.
Next Obligation.
  destruct ge; simpl in *.
  rewrite PTree.gsspec in H. rewrite PTree.gsspec in H0.
  destruct (peq id1 i); destruct (peq id2 i).
  congruence.
  inv H. eelim Plt_strict. eapply genv_symb_range0; eauto.
  inv H0. eelim Plt_strict. eapply genv_symb_range0; eauto.
  eauto.
Qed.

Definition add_globals (ge: t) (gl: list (ident * globdef F V)) : t :=
  List.fold_left add_global gl ge.

Lemma add_globals_app:
  forall gl2 gl1 ge,
  add_globals ge (gl1 ++ gl2) = add_globals (add_globals ge gl1) gl2.
Proof.
  intros. apply fold_left_app. 
Qed.

Program Definition empty_genv (pub: list ident): t :=
  @mkgenv pub (PTree.empty _) (PTree.empty _) 1%positive _ _ _.
Next Obligation.
  rewrite PTree.gempty in H. discriminate.
Qed.
Next Obligation.
  rewrite PTree.gempty in H. discriminate.
Qed.
Next Obligation.
  rewrite PTree.gempty in H. discriminate.
Qed.

Definition globalenv (p: program F V) :=
  add_globals (empty_genv p.(prog_public)) p.(prog_defs).