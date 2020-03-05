Require Import VST.floyd.proofauto.
Require Import fastpile.
Require Import spec_stdlib.

Record PilePredicates := {
  pilerep: list Z -> val -> mpred;
  pilerep_local_facts: forall sigma p,
    pilerep sigma p |-- !! (isptr p /\ Forall (Z.le 0) sigma);
  pilerep_valid_pointer: forall sigma p,
    pilerep sigma p |-- valid_pointer p;
  pile_freeable (p: val) : mpred (*maybe expose the definition of this as malloc_token? Preferably NOT*)
}.

Hint Resolve pilerep_local_facts : saturate_local.
Hint Resolve pilerep_valid_pointer : valid_pointer.

Definition sumlist : list Z -> Z := List.fold_right Z.add 0.

(*Clients -- apile.v and onepile.v -- also need these lemmas:
Lemma pile_new_aux PILE gx x ret:
(EX p : val, PROP ( )  LOCAL (temp ret_temp p)  SEP (pilerep PILE [] p; pile_freeable PILE p; mem_mgr x))%assert (make_ext_rval gx ret)
  |-- !! is_pointer_or_null (force_val ret).
Proof.
 rewrite exp_unfold. Intros p.
 rewrite <- insert_local.
 rewrite lower_andp.
 apply derives_extract_prop; intro.
 destruct H; unfold_lift in H. rewrite retval_ext_rval in *.
 subst p. renormalize. entailer!.
Qed.

Lemma pile_count_aux PILE gx l v ret:
  (PROP ( )  LOCAL (temp ret_temp (Vint (Int.repr (sumlist l))))  SEP (pilerep PILE l v)) (make_ext_rval gx ret)
  |-- !! is_int I32 Signed (force_val ret).
Proof.
 rewrite <- insert_local.
 rewrite lower_andp.
 apply derives_extract_prop; intro.
 destruct H; unfold_lift in H. rewrite retval_ext_rval in *.
 rewrite <- H. renormalize. 
Qed.*)

Definition tpile := Tstruct _pile noattr.

Local Open Scope assert.

Section PileASI.
Variable PILE:PilePredicates.

Definition Pile_new_spec :=
 DECLARE _Pile_new
 WITH gv: globals
 PRE [ ] PROP() (PARAMS () GLOBALS (gv) (SEP(mem_mgr gv)))
 POST[ tptr tpile ]
   EX p: val,
      PROP() LOCAL(temp ret_temp p)
      SEP(pilerep PILE nil p; pile_freeable PILE p; mem_mgr gv).

Definition Pile_add_spec :=
 DECLARE _Pile_add
 WITH p: val, n: Z, sigma: list Z, gv: globals
 PRE [ tptr tpile, tint  ]
    PROP(0 <= n <= Int.max_signed)
    PARAMS (p; Vint (Int.repr n)) GLOBALS (gv)
    SEP(pilerep PILE sigma p; mem_mgr gv)
 POST[ tvoid ]
    PROP() LOCAL()
    SEP(pilerep PILE (n::sigma) p; mem_mgr gv).

Definition Pile_count_spec :=
 DECLARE _Pile_count
 WITH p: val, sigma: list Z
 PRE [ tptr tpile  ]
    PROP(0 <= sumlist sigma <= Int.max_signed)
    PARAMS (p) GLOBALS ()
    SEP (pilerep PILE sigma p)
 POST[ tint ]
      PROP() 
      LOCAL(temp ret_temp (Vint (Int.repr (sumlist sigma))))
      SEP(pilerep PILE sigma p).

Definition Pile_free_spec :=
 DECLARE _Pile_free
 WITH p: val, sigma: list Z, gv: globals
 PRE [ tptr tpile  ]
    PROP()
    PARAMS (p) (GLOBALS (gv)
    SEP(pilerep PILE sigma p; pile_freeable PILE p; mem_mgr gv))
 POST[ tvoid ]
     PROP() LOCAL() SEP(mem_mgr gv).

Definition PileASI:funspecs := [ Pile_new_spec; Pile_add_spec; Pile_count_spec; Pile_free_spec].

End PileASI.
