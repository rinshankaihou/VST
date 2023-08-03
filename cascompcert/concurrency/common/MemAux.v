Require Import Streams Maps Values Blockset GMemory Footprint.


Definition freelist : Type := Stream block.

Definition in_fl (fl: freelist) (b: block) := exists n, Str_nth n fl = b.

Definition get_block (fl: freelist) (n: nat) := Str_nth n fl.

(* stream properties *)
Inductive norep {A: Type} (x: Stream A) : Prop :=
  Norep : (forall n1 n2, n1 <> n2 -> Str_nth n1 x <> Str_nth n2 x) -> norep x.

Inductive disj {A: Type} (x1 x2: Stream A) : Prop :=
  Disj : (forall n1 n2, Str_nth n1 x1 <> Str_nth n2 x2 ) -> disj x1 x2.

Ltac decomp_in_fl :=
  match goal with
  | [H: in_fl _ _ |- _ ]=>
    let x := fresh "n" in
    destruct H as [x H]
  end.

Ltac unfold_fl:=
  repeat decomp_in_fl;
  unfold in_fl, get_block in *.


Definition no_overlap (fl: freelist) (bs:Bset.t) : Prop :=
  forall b n, Str_nth n fl = b -> ~ Bset.belongsto bs b.

(* 1. block validity are unchanged *)
(* 2. block perm/contents are unchanged *)
Definition unchg_freelist (fl: freelist) (gm gm': gmem): Prop :=
  GMem.unchanged_on (fun b ofs => in_fl fl b) gm gm'.

Lemma unchg_freelist_trans:
  forall fl gm1 gm2 gm3,
    unchg_freelist fl gm1 gm2 ->
    unchg_freelist fl gm2 gm3 ->
    unchg_freelist fl gm1 gm3.
Proof.
  intros.
  eapply GMem.unchanged_on_trans; eauto.
Qed.
  
  
Definition valid_block_bset (gm: gmem) : Bset.t := GMem.valid_block gm.
Lemma valid_block_bset_eq:
  forall gm b,
    (GMem.valid_block gm b) <-> (Bset.belongsto (valid_block_bset gm) b).
Proof. firstorder. Qed.



Lemma bset_eq_no_overlap:
  forall bs1 bs2 fl,
    (forall b, bs1 b <-> bs2 b) ->
    no_overlap fl bs1 <-> no_overlap fl bs2.
Proof.
  clear. intros.
  unfold no_overlap, Bset.belongsto.
  split; intros; [rewrite <-H | rewrite H]; eauto.
Qed.
