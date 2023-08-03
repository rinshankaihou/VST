Require Import Coqlib.
Require Import Integers.
Require Import Floats.
Require Import Values.

Require Import Footprint Memory MemOpFP.

Local Notation locset := Locs.t.
Local Notation empls := Locs.emp.
Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.
Local Notation FP := FP.Build_t.

(** TODO: should be moved to another file, eg. Val_fp *)
Definition cmpu_bool_fp (m: mem) (c: comparison) (v1 v2: val): option footprint :=
  match v1, v2 with
  | Vint _, Vint _ => Some empfp
  | Vint n1, Vptr b2 ofs2 =>
    if Archi.ptr64 then None
    else if Int.eq n1 Int.zero
         then if Val.cmp_different_blocks c
              then Some (weak_valid_pointer_fp m b2 (Ptrofs.unsigned ofs2))
              else None
         else None
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
    if Archi.ptr64 then None
    else if eq_block b1 b2
         then Some (FP.union (weak_valid_pointer_fp m b1 (Ptrofs.unsigned ofs1))
                             (weak_valid_pointer_fp m b2 (Ptrofs.unsigned ofs2)))
         else if Val.cmp_different_blocks c
              then Some (FP.union (valid_pointer_fp b1 (Ptrofs.unsigned ofs1))
                                  (valid_pointer_fp b2 (Ptrofs.unsigned ofs2)))
              else None
  | Vptr b1 ofs1, Vint n2 =>
    if Archi.ptr64 then None
    else if Int.eq n2 Int.zero
         then if Val.cmp_different_blocks c
              then Some (weak_valid_pointer_fp m b1 (Ptrofs.unsigned ofs1))
              else None
         else None
  | _, _ => None
  end.
Definition cmpu_bool_fp_total (m: mem) (c: comparison) (v1 v2: val) : footprint :=
  match v1, v2 with
  | Vint _, Vint _ => empfp
  | Vint n1, Vptr b2 ofs2 =>
    if Archi.ptr64 then empfp
    else if Int.eq n1 Int.zero
         then if Val.cmp_different_blocks c                   
              then (weak_valid_pointer_fp m b2 (Ptrofs.unsigned ofs2))
              else empfp
         else empfp
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
    if Archi.ptr64 then empfp
    else if eq_block b1 b2
         then (FP.union (weak_valid_pointer_fp m b1 (Ptrofs.unsigned ofs1))
                        (weak_valid_pointer_fp m b2 (Ptrofs.unsigned ofs2)))
         else if Val.cmp_different_blocks c
              then (FP.union (valid_pointer_fp b1 (Ptrofs.unsigned ofs1))
                             (valid_pointer_fp b2 (Ptrofs.unsigned ofs2)))
              else empfp
  | Vptr b1 ofs1, Vint n2 =>
    if Archi.ptr64 then empfp
    else if Int.eq n2 Int.zero
         then if Val.cmp_different_blocks c
              then (weak_valid_pointer_fp m b1 (Ptrofs.unsigned ofs1))
              else empfp
         else empfp
(*  | Vptr b1 ofs1, Vundef =>
    if Archi.ptr64 then empfp
    else weak_valid_pointer_fp m b1 (Ptrofs.unsigned ofs1)
  | Vundef, Vptr b2 ofs2 =>
    if Archi.ptr64 then empfp
    else weak_valid_pointer_fp m b2 (Ptrofs.unsigned ofs2) *)
  | _, _ => empfp
  end.

Lemma cmpu_bool_fp_cmpu_bool_fp_total:
  forall m c v1 v2 fp,
    cmpu_bool_fp m c v1 v2 = Some fp ->
    cmpu_bool_fp_total m c v1 v2 = fp.
Proof.
  unfold cmpu_bool_fp, cmpu_bool_fp_total; intros.
  destruct v1; try congruence;
    destruct v2; try congruence;
      repeat match goal with
             | H: context[match ?x with _ => _ end] |- _ =>
               destruct x eqn:?; try congruence
             end.
Qed.
  
Lemma cmpu_bool_cmpu_bool_fp:
  forall m c v1 v2 b,
    Val.cmpu_bool (Mem.valid_pointer m) c v1 v2 = Some b ->
    exists fp, cmpu_bool_fp m c v1 v2 = Some fp.
Proof.
  unfold Val.cmpu_bool, cmpu_bool_fp; intros.
  destruct v1, v2, Archi.ptr64;
    try destruct eq_block;
    try destruct Val.cmp_different_blocks;
    repeat destruct (Int.eq _ Int.zero);
    try (inv H; eauto; fail);
    match goal with H: context[if ?x then _ else _] |- _ => destruct x; inv H end .
Qed.

Lemma cmpu_bool_cmpu_bool_fp_total:
  forall m c v1 v2 b,
    Val.cmpu_bool (Mem.valid_pointer m) c v1 v2 = Some b ->
    exists fp, cmpu_bool_fp_total m c v1 v2 = fp.
Proof.
  intros; exploit cmpu_bool_cmpu_bool_fp. eauto. clear.
  intros [fp H]. exists fp.
  apply cmpu_bool_fp_cmpu_bool_fp_total. auto.
Qed.

Lemma cmpu_bool_fp_cmpu_bool:
  forall m c v1 v2 fp,
    let valid := Mem.valid_pointer m in
    let weak_valid := fun b ofs => valid b ofs || valid b (ofs - 1) in
    cmpu_bool_fp m c v1 v2 = Some fp ->
    (exists b, Val.cmpu_bool valid c v1 v2 = Some b)
    \/ (exists b1 ofs1 b2 ofs2, v1 = Vptr b1 ofs1 /\ v2 = Vptr b2 ofs2
                          /\ ((b1 = b2
                              /\ (weak_valid b1 (Ptrofs.unsigned ofs1) = false
                                 \/ weak_valid b2 (Ptrofs.unsigned ofs2) = false))
                             \/ (b1 <> b2
                                /\ (valid b1 (Ptrofs.unsigned ofs1) = false
                                   \/ valid b2 (Ptrofs.unsigned ofs2) = false))))
    \/ (exists n1 b2 ofs2, v1 = Vint n1 /\ v2 = Vptr b2 ofs2
                     /\ weak_valid b2 (Ptrofs.unsigned ofs2) = false)
    \/ (exists b1 ofs1 n2, v1 = Vptr b1 ofs1 /\ v2 = Vint n2
                     /\ weak_valid b1 (Ptrofs.unsigned ofs1) = false).
Proof.
  unfold Val.cmpu_bool, cmpu_bool_fp; intros.
  destruct v1, v2, Archi.ptr64;
    try destruct eq_block;  
    try destruct Val.cmp_different_blocks eqn:?; 
    repeat match goal with
           | |- context[Int.eq ?x Int.zero] => destruct (Int.eq x Int.zero) eqn:? end;
    try (inv H; fail); eauto;
      repeat match goal with
             | |- context[Mem.valid_pointer m ?b ?x] =>
               destruct (Mem.valid_pointer m b x) eqn:?; simpl; try discriminate; eauto
             | |- (exists b1, None = Some _) \/ _ => right
             | |- (exists _ _ _ _, Vptr _ _ = Vptr _ _ /\ Vptr _ _ = Vptr _ _ /\ _) \/ _ =>
               left; do 4 eexists; split; [eauto| split ; [eauto |]]
             | |- (exists _ _ _ _, Vint _ = Vptr _ _ /\ _) \/ _ =>
               right; left; do 3 eexists; split; [eauto| split; [eauto|]]
             | |- (exists _ _ _ _, _ /\ Vint _ = Vptr _ _ /\ _) \/ _ =>
               right; right; do 3 eexists; split; [eauto| split; [eauto|]]
             end.
Qed.
  
Definition cmplu_bool_fp (m: mem) (c: comparison) (v1 v2: val) : option footprint :=
  match v1, v2 with
  | Vlong _, Vlong _ => Some empfp
  | Vlong n1, Vptr b2 ofs2 =>
    if negb Archi.ptr64 then None
    else if Int64.eq n1 Int64.zero
         then if Val.cmp_different_blocks c
              then Some (weak_valid_pointer_fp m b2 (Ptrofs.unsigned ofs2))
              else None
         else None
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
    if negb Archi.ptr64 then None
    else if eq_block b1 b2
         then Some (FP.union (weak_valid_pointer_fp m b1 (Ptrofs.unsigned ofs1))
                             (weak_valid_pointer_fp m b2 (Ptrofs.unsigned ofs2)))
         else if Val.cmp_different_blocks c
              then Some (FP.union (valid_pointer_fp b1 (Ptrofs.unsigned ofs1))
                                  (valid_pointer_fp b2 (Ptrofs.unsigned ofs2)))
              else None
  | Vptr b1 ofs1, Vlong n2 =>
    if negb Archi.ptr64 then None
    else if Int64.eq n2 Int64.zero
         then if Val.cmp_different_blocks c
              then Some (weak_valid_pointer_fp m b1 (Ptrofs.unsigned ofs1))
              else None
         else None
  | _, _ => None
  end.

Definition cmplu_bool_fp_total (m: mem) (c: comparison) (v1 v2: val) : footprint :=
  match v1, v2 with
  | Vlong n1, Vptr b2 ofs2 =>
    if negb Archi.ptr64 then empfp
    else if Int64.eq n1 Int64.zero
         then if Val.cmp_different_blocks c
              then (weak_valid_pointer_fp m b2 (Ptrofs.unsigned ofs2))
              else empfp
         else empfp
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
    if negb Archi.ptr64 then empfp
    else if eq_block b1 b2
         then (FP.union (weak_valid_pointer_fp m b1 (Ptrofs.unsigned ofs1))
                        (weak_valid_pointer_fp m b2 (Ptrofs.unsigned ofs2)))
         else if Val.cmp_different_blocks c
              then (FP.union (valid_pointer_fp b1 (Ptrofs.unsigned ofs1))
                                  (valid_pointer_fp b2 (Ptrofs.unsigned ofs2)))
              else empfp
  | Vptr b1 ofs1, Vlong n2 =>
    if negb Archi.ptr64 then empfp
    else if Int64.eq n2 Int64.zero
         then if Val.cmp_different_blocks c
              then (weak_valid_pointer_fp m b1 (Ptrofs.unsigned ofs1))
              else empfp
         else empfp
  | _, _ => empfp
  end.

Lemma cmplu_bool_fp_cmplu_bool_fp_total:
  forall m c v1 v2 fp,
    cmplu_bool_fp m c v1 v2 = Some fp ->
    cmplu_bool_fp_total m c v1 v2 = fp.
Proof.
  unfold cmplu_bool_fp, cmplu_bool_fp_total; intros.
  destruct v1; try congruence;
    destruct v2; try congruence;
      repeat match goal with
             | H: context[match ?x with _ => _ end] |- _ =>
               destruct x eqn:?; try congruence
             end.
Qed.

Lemma cmplu_bool_cmplu_bool_fp:
  forall m c v1 v2 b,
    Val.cmplu_bool (Mem.valid_pointer m) c v1 v2 = Some b ->
    exists fp, cmplu_bool_fp m c v1 v2 = Some fp.
Proof.
  unfold Val.cmplu_bool, cmplu_bool_fp; intros.
  destruct v1, v2, Archi.ptr64;
    try destruct eq_block;
    try destruct Val.cmp_different_blocks;
    repeat destruct (Int64.eq _ Int64.zero);
    try (inv H; eauto; fail);
    repeat match goal with H: context[if ?x then _ else _] |- _ => destruct x; eauto; inv H end.
Qed.

Lemma cmplu_bool_fp_cmplu_bool:
  forall m c v1 v2 fp,
    let valid:= Mem.valid_pointer m in
    let weak_valid := fun b ofs => valid b ofs || valid b (ofs - 1) in
    cmplu_bool_fp m c v1 v2 = Some fp ->
    (exists b, Val.cmplu_bool valid c v1 v2 = Some b)
    \/ (exists b1 ofs1 b2 ofs2, v1 = Vptr b1 ofs1 /\ v2 = Vptr b2 ofs2
                          /\ ((b1 = b2
                              /\ (weak_valid b1 (Ptrofs.unsigned ofs1) = false
                                 \/ weak_valid b2 (Ptrofs.unsigned ofs2) = false))
                             \/ (b1 <> b2
                                /\ (valid b1 (Ptrofs.unsigned ofs1) = false
                                   \/ valid b2 (Ptrofs.unsigned ofs2) = false))))
    \/ (exists n1 b2 ofs2, v1 = Vlong n1 /\ v2 = Vptr b2 ofs2
                     /\ weak_valid b2 (Ptrofs.unsigned ofs2) = false)
    \/ (exists b1 ofs1 n2, v1 = Vptr b1 ofs1 /\ v2 = Vlong n2
                     /\ weak_valid b1 (Ptrofs.unsigned ofs1) = false).
Proof.
  unfold Val.cmplu_bool, cmplu_bool_fp; intros.
  destruct v1, v2, Archi.ptr64;
    try destruct eq_block;  
    try destruct Val.cmp_different_blocks eqn:?; 
    repeat match goal with
           | |- context[Int64.eq ?x Int64.zero] => destruct (Int64.eq x Int64.zero) eqn:? end;
    try (inv H; fail); eauto;
      repeat match goal with
             | |- context[Mem.valid_pointer m ?b ?x] =>
               destruct (Mem.valid_pointer m b x) eqn:?; simpl; try discriminate; eauto
             | |- (exists b1, None = Some _) \/ _ => right
             | |- (exists _ _ _ _, Vptr _ _ = Vptr _ _ /\ Vptr _ _ = Vptr _ _ /\ _) \/ _ =>
               left; do 4 eexists; split; [eauto| split ; [eauto |]]
             | |- (exists _ _ _ _, Vlong _ = Vptr _ _ /\ _) \/ _ =>
               right; left; do 3 eexists; split; [eauto| split; [eauto|]]
             | |- (exists _ _ _ _, _ /\ Vlong _ = Vptr _ _ /\ _) \/ _ =>
               right; right; do 3 eexists; split; [eauto| split; [eauto|]]
             end.
Qed.