Require Import Values Globalenvs Blockset Injections LDSimDefs.

(** f' won't inject anything more than f injects to f's range *)
Definition sep_inject (f f': meminj) : Prop :=
  forall b b' b_img ofs1 ofs2,
    f b = Some (b_img, ofs1) ->
    f' b' = Some (b_img, ofs2) ->
    f b' = Some (b_img, ofs2).

(** TODO: Should be a generic predicate *)
Record proper_mu {F1 V1 F2 V2: Type}
       (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2)
       (j: meminj) (mu: Mu) : Prop :=
  { proper_mu_inject: Bset.inject (inj mu) (SharedSrc mu) (SharedTgt mu);
    proper_mu_ge_init_inj: LDSimDefs.ge_init_inj mu ge1 ge2;
    proper_mu_inject_incr: inject_incr (Bset.inj_to_meminj (inj mu)) j;
    proper_mu_sep_inject: sep_inject (Bset.inj_to_meminj (inj mu)) j;
  }.
