Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Ctypes.

Require Import Cop.

Require Import Footprint Memory MemOpFP ValFP.

Local Notation locset := Locs.t.
Local Notation empls := Locs.emp.
Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.
Local Notation FP := FP.Build_t.

(** Instrument C operations with footprints *)
(** * Semantic with memory read/writes *)
Definition sem_cast_fp (v:val) (t1 t2: type) (m: mem): option footprint :=
  match classify_cast t1 t2 with
  | cast_case_pointer =>
    match v with
    | Vint _ => if Archi.ptr64 then None else Some empfp
    | Vlong _ => if Archi.ptr64 then Some empfp else None
    | Vptr _ _ => Some empfp
    | _ => None
    end
  | cast_case_i2i _ _ =>
    match v with
    | Vint _ => Some empfp
    | _ => None
    end
  | cast_case_f2f =>
    match v with
    | Vfloat _ => Some empfp
    | _ => None
    end
  | cast_case_s2s =>
    match v with
    | Vsingle _ => Some empfp
    | _ => None
    end
  | cast_case_f2s =>
    match v with
    | Vfloat _ => Some empfp
    | _ => None
    end
  | cast_case_s2f =>
    match v with
    | Vsingle _ => Some empfp
    | _ => None
    end
  | cast_case_i2f _ =>
    match v with
    | Vint _ => Some empfp
    | _ => None
    end
  | cast_case_i2s _ =>
    match v with
    | Vint _ => Some empfp
    | _ => None
    end
  | cast_case_f2i sz2 si2 =>
    match v with
    | Vfloat f =>
      match cast_float_int si2 f with
      | Some _ => Some empfp
      | None => None
      end
    | _ => None
    end
  | cast_case_s2i sz2 si2 =>
    match v with
    | Vsingle f =>
      match cast_single_int si2 f with
      | Some _ => Some empfp
      | None => None
      end
    | _ => None
    end
  | cast_case_l2l =>
    match v with
    | Vlong _ => Some empfp
    | _ => None
    end
  | cast_case_i2l _ =>
    match v with
    | Vint _ => Some empfp
    | _ => None
    end
  | cast_case_l2i _ _ =>
    match v with
    | Vlong _ => Some empfp
    | _ => None
    end
  | cast_case_l2f _ =>
    match v with
    | Vlong _ => Some empfp
    | _ => None
    end
  | cast_case_l2s _ =>
    match v with
    | Vlong _ => Some empfp
    | _ => None
    end
  | cast_case_f2l si2 =>
    match v with
    | Vfloat f =>
      match cast_float_long si2 f with
      | Some _ => Some empfp
      | None => None
      end
    | _ => None
    end
  | cast_case_s2l si2 =>
    match v with
    | Vsingle f =>
      match cast_single_long si2 f with
      | Some i => Some empfp
      | None => None
      end
    | _ => None
    end
  | cast_case_i2bool =>
    match v with
    | Vptr b ofs =>
      if Archi.ptr64 then None
      else Some (weak_valid_pointer_fp m b (Ptrofs.unsigned ofs))
    | Vint n => Some empfp
    | _ => None
    end
  | cast_case_l2bool =>
    match v with
    | Vptr b ofs =>
      if negb Archi.ptr64 then None
      else Some (weak_valid_pointer_fp m b (Ptrofs.unsigned ofs))
    | Vlong _ => Some empfp
    | _ => None
    end
  | cast_case_f2bool =>
    match v with
    | Vfloat _ => Some empfp
    | _ => None
    end
  | cast_case_s2bool =>
    match v with
    | Vsingle _ => Some empfp
    | _ => None
    end
  | cast_case_struct id1 id2 =>
    match v with
    | Vptr _ _ => if ident_eq id1 id2 then Some empfp else None
    | _ => None
    end
  | cast_case_union id1 id2 =>
    match v with
    | Vptr _ _ => if ident_eq id1 id2 then Some empfp else None
    | _ => None
    end
  | cast_case_void => Some empfp
  | case_case_default => None
  end.

Definition sem_cast_fp_total (v:val) (t1 t2: type) (m: mem): footprint :=
  match classify_cast t1 t2 with
  | cast_case_i2bool =>
    match v with
    | Vptr b ofs =>
      if Archi.ptr64 then empfp
      else (weak_valid_pointer_fp m b (Ptrofs.unsigned ofs))
    | _ => empfp
    end
  | cast_case_l2bool =>
    match v with
    | Vptr b ofs =>
      if negb Archi.ptr64 then empfp
      else (weak_valid_pointer_fp m b (Ptrofs.unsigned ofs))
    | _ => empfp
    end
  | _ => empfp
  end.

Lemma sem_cast_fp_sem_cast_fp_total:
  forall v t1 t2 m fp,
    sem_cast_fp v t1 t2 m = Some fp ->
    sem_cast_fp_total v t1 t2 m = fp.
Proof.
  unfold sem_cast_fp, sem_cast_fp_total; intros.
  destruct classify_cast;
    repeat match goal with
           | H: match ?x with _ => _ end = Some _ |- _ =>
             let Hx := fresh in
             destruct x eqn:?; try inversion Hx
           | H: Some _ = Some _ |- _ => inv H; auto
           | H: None = Some _ |- _ => discriminate
           end.
Qed.

Lemma sem_cast_sem_cast_fp:
  forall v1 ty1 ty2 m v2,
    sem_cast v1 ty1 ty2 m = Some v2 ->
    exists fp, sem_cast_fp v1 ty1 ty2 m = Some fp.
Proof.
  unfold sem_cast, sem_cast_fp.
  intros.
  destruct (classify_cast ty1 ty2) eqn:? ; eauto;
    destruct v1 eqn:? ; try congruence; eauto;
      match goal with
      | |- context[match ?x with _ => _ end] => destruct x; try congruence; eauto
      end.
Qed.

Lemma sem_cast_sem_cast_fp_total:
  forall v1 ty1 ty2 m v2,
    sem_cast v1 ty1 ty2 m = Some v2 ->
    exists fp, sem_cast_fp_total v1 ty1 ty2 m = fp.
Proof.
  intros. exploit sem_cast_sem_cast_fp; eauto.
Qed.

Lemma sem_cast_fp_sem_cast:
  forall v1 ty1 ty2 m fp,
    sem_cast_fp v1 ty1 ty2 m = Some fp ->
    (exists v2, sem_cast v1 ty1 ty2 m = Some v2)
    \/ (exists b ofs, v1 = Vptr b ofs /\ Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) = false).
Proof.
  unfold sem_cast_fp, sem_cast. intros.
  destruct (classify_cast ty1 ty2) eqn:? ; eauto;
    destruct v1 eqn:? ; try congruence; eauto;
      match goal with
      | |- context[match ?x with _ => _ end] => destruct x eqn:? ; try congruence; eauto
      end;
      match goal with
      | |- context[match ?x with _ => _ end] => destruct x eqn:? ; eauto
      end.
Qed.

Lemma sem_cast_casted_fp:
  forall v ty m,
    val_casted v ty ->
    sem_cast v ty ty m = Some v ->
    sem_cast_fp v ty ty m = Some empfp.
Proof.
  intros v ty m CASTED CAST.
  destruct v; inversion CASTED; subst; try (cbv; auto; fail);
    unfold sem_cast_fp, sem_cast in *.
  destruct classify_cast; eauto; inv CAST.
  simpl in *. rewrite H0. auto.
  simpl in *. rewrite H2. auto.
  simpl in *. destruct ident_eq; auto; discriminate.
  simpl in *. destruct ident_eq; auto; discriminate.
Qed.

(** Interpretation of values as truth values. *)
Definition bool_val_fp (v: val) (t: type) (m: mem): option footprint :=
  match classify_bool t with
  | bool_case_i =>
    match v with
    | Vptr b ofs =>
      if Archi.ptr64 then None
      else Some (weak_valid_pointer_fp m b (Ptrofs.unsigned ofs))
    | Vint n => Some empfp
    | _ => None
    end
  | bool_case_l =>
    match v with
    | Vptr b ofs =>
      if negb Archi.ptr64 then None
      else Some (weak_valid_pointer_fp m b (Ptrofs.unsigned ofs))
    | Vlong _ => Some empfp
    | _ => None
    end
  | bool_case_f =>
    match v with
    | Vfloat _ => Some empfp
    | _ => None
    end
  | bool_case_s =>
    match v with
    | Vsingle _ => Some empfp
    | _ => None
    end
  | bool_defalt => None
  end.

Definition bool_val_fp_total (v: val) (t: type) (m: mem): footprint :=
  match classify_bool t with
  | bool_case_i =>
    match v with
    | Vptr b ofs =>
      if Archi.ptr64 then empfp
      else (weak_valid_pointer_fp m b (Ptrofs.unsigned ofs))
    | _ => empfp
    end
  | bool_case_l =>
    match v with
    | Vptr b ofs =>
      if negb Archi.ptr64 then empfp
      else (weak_valid_pointer_fp m b (Ptrofs.unsigned ofs))
    | _ => empfp
    end
  | _ => empfp
  end.

Lemma bool_val_fp_bool_val_fp_total:
  forall v t m fp,
    bool_val_fp v t m = Some fp ->
    bool_val_fp_total v t m = fp.
Proof.
  unfold bool_val_fp, bool_val_fp_total; intros.
  destruct Archi.ptr64, classify_bool, v; inv H; auto.
Qed.

Lemma bool_val_bool_val_fp:
  forall v t m b,
    bool_val v t m = Some b ->
    exists fp, bool_val_fp v t m = Some fp.
Proof.
  unfold bool_val, bool_val_fp; intros.
  destruct Archi.ptr64 eqn:? ;
    destruct (classify_bool t); destruct v; simpl in *;
      try congruence; eauto.
Qed.

Lemma bool_val_bool_val_fp_total:
  forall v t m b,
    bool_val v t m = Some b ->
    exists fp, bool_val_fp_total v t m = fp.
Proof.
  intros; exploit bool_val_bool_val_fp; eauto.
Qed.

Lemma bool_val_fp_bool_val:
  forall v t m fp,
    bool_val_fp v t m = Some fp ->
    (exists b, bool_val v t m = Some b) 
    \/ (exists b ofs, v = Vptr b ofs /\ Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) = false).
Proof.
  unfold bool_val, bool_val_fp; intros.
  destruct Archi.ptr64 eqn:? ;
    destruct (classify_bool t); destruct v; simpl in *;
      try congruence; eauto;
        match goal with
        | |- context[if ?x then _ else _] => destruct x eqn:? ; eauto
        end.
Qed.


  

(** ** Unary operators *)

(** *** Boolean negation *)

Definition sem_notbool_fp (v: val) (ty: type) (m: mem) : option footprint :=
  bool_val_fp v ty m.

Lemma sem_notbool_sem_notbool_fp:
  forall v ty m b,
    sem_notbool v ty m = Some b ->
    exists fp, sem_notbool_fp v ty m = Some fp.
Proof.
  unfold sem_notbool, sem_notbool_fp.
  unfold option_map. intros.
  destruct (bool_val) eqn:?; inv H.
  eapply bool_val_bool_val_fp; eauto.
Qed.

Lemma sem_notbool_fp_sem_notbool:
  forall v ty m fp,
    sem_notbool_fp v ty m = Some fp ->
    (exists b, sem_notbool v ty m = Some b)
    \/ (exists b ofs, v = Vptr b ofs /\ Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) = false).
Proof.
  unfold sem_notbool, sem_notbool_fp, option_map. intros.
  apply bool_val_fp_bool_val with v ty m fp in H.
  destruct H; auto. inv H. rewrite H0. eauto.
Qed.


(** ** Binary operators *)
Definition sem_binarith_fp
           (sem_int: signedness -> int -> int -> option val)
           (sem_long: signedness -> int64 -> int64 -> option val)
           (sem_float: float -> float -> option val)
           (sem_single: float32 -> float32 -> option val)
           (v1: val) (t1: type) (v2: val) (t2: type) (m: mem): option footprint:=
  let c := classify_binarith t1 t2 in
  let t := binarith_type c in
  match sem_cast v1 t1 t m , sem_cast_fp v1 t1 t m with
  | Some v1', Some fp1 =>
    match sem_cast v2 t2 t m , sem_cast_fp v2 t2 t m with
    | Some v2', Some fp2 =>
      match c with
      | bin_case_i sg =>
        match v1', v2' with
        | Vint n1, Vint n2 =>
          if sem_int sg n1 n2 then Some (FP.union fp1 fp2) else None
        | _,  _ => None
        end
      | bin_case_f =>
        match v1', v2' with
        | Vfloat n1, Vfloat n2 =>
          if sem_float n1 n2 then Some (FP.union fp1 fp2) else None
        | _,  _ => None
        end
      | bin_case_s =>
        match v1', v2' with
        | Vsingle n1, Vsingle n2 =>
          if sem_single n1 n2 then Some (FP.union fp1 fp2) else None
        | _,  _ => None
        end
      | bin_case_l sg =>
        match v1', v2' with
        | Vlong n1, Vlong n2 =>
          if sem_long sg n1 n2 then Some (FP.union fp1 fp2) else None            
        | _,  _ => None
        end
      | bin_default => None
      end
    | _, _ => None
    end
  | _, _ => None
  end.

Lemma sem_binarith_sem_binarith_fp:
  forall sem1 sem2 sem3 sem4 v1 t1 v2 t2 m v,
    sem_binarith sem1 sem2 sem3 sem4 v1 t1 v2 t2 m = Some v ->
    exists fp, sem_binarith_fp sem1 sem2 sem3 sem4 v1 t1 v2 t2 m = Some fp.
Proof.
  unfold sem_binarith, sem_binarith_fp.
  intros; destruct (sem_cast v2 t2 _ m) eqn:?, (sem_cast v1 t1 _ m) eqn:?; simpl in *.
  do 2 match goal with
       | H: sem_cast _ _ _ _ = Some _ |- _ =>
         apply sem_cast_sem_cast_fp in H; destruct H as [? H]; rewrite H
       end.
  destruct (classify_binarith t1 t2); simpl in *; eauto;
    destruct v3, v0; inv H; rewrite H1; eauto.
  inv H.
  inv H.
  inv H.
Qed.
  
Lemma sem_binarith_fp_sem_binarith:
  forall sem1 sem2 sem3 sem4 v1 t1 v2 t2 m fp,
    sem_binarith_fp sem1 sem2 sem3 sem4 v1 t1 v2 t2 m = Some fp ->
    (exists v, sem_binarith sem1 sem2 sem3 sem4 v1 t1 v2 t2 m = Some v)
    \/ (exists b ofs, v1 = Vptr b ofs /\ Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) = false)
    \/ (exists b ofs, v2 = Vptr b ofs /\ Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) = false).
Proof.
  unfold sem_binarith_fp, sem_binarith.
  intros.
  destruct (sem_cast_fp v2 t2) eqn: Hv2, (sem_cast_fp v1 t1) eqn: Hv1; simpl;
    try (apply sem_cast_fp_sem_cast with (m:=m) in Hv2);
    try (destruct Hv2 as [ [v2' Hv2] | [b [ofs [Hv2 INVALID2]]]];
         [ rewrite Hv2 in * | ]);
    try (apply sem_cast_fp_sem_cast with (m:=m) in Hv1);
    try (destruct Hv1 as [ [v1' Hv1] | [b [ofs [Hv1 INVALID1]]]];
         [ rewrite Hv1 in * | ]);
    destruct classify_binarith;
    try destruct v1' eqn:?; try destruct v2' eqn:?; try (inv H; fail);
      try match goal with
          | H: (if ?x then _ else _) = Some _ |- _ => destruct x; inv H; eauto
          end; eauto;
        try (right; left; eauto; fail);
        try (right; right; eauto; fail).
Qed.

(** *** Addition *) 
Definition sem_add_fp
           (cenv: composite_env) (v1:val) (t1:type) (v2: val) (t2:type)
           (m: mem) : option footprint :=
  match classify_add t1 t2 with
  | add_case_pi ty si =>
    if sem_add_ptr_int cenv ty si v1 v2
    then Some empfp else None
  | add_case_pl ty =>
    if sem_add_ptr_long cenv ty v1 v2
    then Some empfp else None
  | add_case_ip si ty =>
    if sem_add_ptr_int cenv ty si v2 v1
    then Some empfp else None
  | add_case_lp ty =>
    if sem_add_ptr_long cenv ty v2 v1
    then Some empfp else None
  | add_default =>
    sem_binarith_fp
      (fun sg n1 n2 => Some(Vint(Int.add n1 n2)))
      (fun sg n1 n2 => Some(Vlong(Int64.add n1 n2)))
      (fun n1 n2 => Some(Vfloat(Float.add n1 n2)))
      (fun n1 n2 => Some(Vsingle(Float32.add n1 n2)))
      v1 t1 v2 t2 m
  end.

Lemma sem_add_sem_add_fp:
  forall cenv v1 t1 v2 t2 m v,
    sem_add cenv v1 t1 v2 t2 m = Some v ->
    exists fp, sem_add_fp cenv v1 t1 v2 t2 m = Some fp.
Proof.
  unfold sem_add, sem_add_fp. intros.
  destruct (classify_add t1 t2); try rewrite H; eauto.
  eapply sem_binarith_sem_binarith_fp; eauto.
Qed.

Lemma sem_add_fp_sem_add:
  forall cenv v1 t1 v2 t2 m fp,
    sem_add_fp cenv v1 t1 v2 t2 m = Some fp ->
    (exists v : val, sem_add cenv v1 t1 v2 t2 m = Some v) \/
    (exists (b : block) (ofs : ptrofs),
        v1 = Vptr b ofs /\ Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) = false) \/
    (exists (b : block) (ofs : ptrofs),
        v2 = Vptr b ofs /\ Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) = false).
Proof.
  unfold sem_add, sem_add_fp. intros.
  destruct (classify_add t1 t2);
    try match goal with
        | H : (if ?x then _ else _) = Some _ |- _ => destruct x; inv H; eauto
        end.
  eapply sem_binarith_fp_sem_binarith; eauto.
Qed.



(** *** Subtraction *)
Definition sem_sub_fp cenv v1 t1 v2 t2 m : option footprint :=
  match classify_sub t1 t2 with
  | sub_case_pi ty si =>
    match v1, v2 with
    | Vptr b1 ofs1, Vint n2 => Some empfp
    | Vint n1, Vint n2 =>
      if Archi.ptr64 then None else Some empfp
    | Vlong n1, Vint n2 =>
      if Archi.ptr64 then Some empfp else None
    | _,  _ => None
      end
  | sub_case_pl ty =>            (**r pointer minus long *)
    match v1, v2 with
    | Vptr b1 ofs1, Vlong n2 => Some empfp
    | Vint n1, Vlong n2 =>
      if Archi.ptr64 then None else Some empfp
    | Vlong n1, Vlong n2 =>
      if Archi.ptr64 then Some empfp else None
    | _,  _ => None
    end
  | sub_case_pp ty =>          (**r pointer minus pointer *)
    match v1,v2 with
    | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if eq_block b1 b2 then
        let sz := sizeof cenv ty in
        if zlt 0 sz && zle sz Ptrofs.max_signed
        then Some empfp
        else None
      else None
    | _, _ => None
    end
  | sub_default =>
      sem_binarith_fp
        (fun sg n1 n2 => Some(Vint(Int.sub n1 n2)))
        (fun sg n1 n2 => Some(Vlong(Int64.sub n1 n2)))
        (fun n1 n2 => Some(Vfloat(Float.sub n1 n2)))
        (fun n1 n2 => Some(Vsingle(Float32.sub n1 n2)))
        v1 t1 v2 t2 m
  end.

Lemma sem_sub_sem_sub_fp:
  forall cenv v1 t1 v2 t2 m v,
    sem_sub cenv v1 t1 v2 t2 m = Some v ->
    exists fp, sem_sub_fp cenv v1 t1 v2 t2 m = Some fp.
Proof.
  unfold sem_sub, sem_sub_fp. intros.
  destruct (classify_sub t1 t2), v1, v2;
    try (inv H; fail);
    try (destruct Archi.ptr64; inv H; eauto; fail);
    try (eapply sem_binarith_sem_binarith_fp; eauto; fail).
  unshelve edestruct eq_block, zlt; inv H; simpl in *.
  destruct proj_sumbool; eauto.
  inv H1.
Qed.

Lemma sem_sub_fp_sem_sub:
  forall cenv v1 t1 v2 t2 m fp,
    sem_sub_fp cenv v1 t1 v2 t2 m = Some fp ->
    (exists v : val, sem_sub cenv v1 t1 v2 t2 m = Some v) \/
    (exists (b : block) (ofs : ptrofs),
        v1 = Vptr b ofs /\ Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) = false) \/
    (exists (b : block) (ofs : ptrofs),
        v2 = Vptr b ofs /\ Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) = false).
Proof.
  unfold sem_sub, sem_sub_fp. intros.
  destruct (classify_sub t1 t2);
    repeat match goal with
           | H : (if ?x then _ else _) = Some _ |- _ => destruct x eqn:?
           | H : context[match ?x with _ => _ end] |- _ => destruct x eqn:?
           | |- context[if ?x then _ else _] => destruct x eqn:?
           end;
    try discriminate; eauto.
  eapply sem_binarith_fp_sem_binarith; eauto.
Qed.


(** *** Multiplication, division, modulus *)
Definition sem_mul_fp (v1:val) (t1:type) (v2: val) (t2:type) (m: mem): option footprint :=
  sem_binarith_fp
    (fun sg n1 n2 => Some(Vint(Int.mul n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.mul n1 n2)))
    (fun n1 n2 => Some(Vfloat(Float.mul n1 n2)))
    (fun n1 n2 => Some(Vsingle(Float32.mul n1 n2)))
    v1 t1 v2 t2 m.

Definition sem_div_fp (v1:val) (t1:type) (v2: val) (t2:type) (m: mem) : option footprint :=
  sem_binarith_fp
    (fun sg n1 n2 =>
       match sg with
       | Signed =>
         if Int.eq n2 Int.zero
            || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
         then None else Some(Vint(Int.divs n1 n2))
       | Unsigned =>
         if Int.eq n2 Int.zero
         then None else Some(Vint(Int.divu n1 n2))
       end)
    (fun sg n1 n2 =>
       match sg with
       | Signed =>
         if Int64.eq n2 Int64.zero
            || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
         then None else Some(Vlong(Int64.divs n1 n2))
       | Unsigned =>
         if Int64.eq n2 Int64.zero
         then None else Some(Vlong(Int64.divu n1 n2))
       end)
    (fun n1 n2 => Some(Vfloat(Float.div n1 n2)))
    (fun n1 n2 => Some(Vsingle(Float32.div n1 n2)))
    v1 t1 v2 t2 m.

Definition sem_mod_fp (v1:val) (t1:type) (v2: val) (t2:type) (m: mem) : option footprint:=
  sem_binarith_fp
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int.eq n2 Int.zero
          || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
          then None else Some(Vint(Int.mods n1 n2))
      | Unsigned =>
          if Int.eq n2 Int.zero
          then None else Some(Vint(Int.modu n1 n2))
      end)
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int64.eq n2 Int64.zero
          || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
          then None else Some(Vlong(Int64.mods n1 n2))
      | Unsigned =>
          if Int64.eq n2 Int64.zero
          then None else Some(Vlong(Int64.modu n1 n2))
      end)
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 t1 v2 t2 m.

Definition sem_and_fp (v1:val) (t1:type) (v2: val) (t2:type) (m: mem) : option footprint:=
   sem_binarith_fp
    (fun sg n1 n2 => Some(Vint(Int.and n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.and n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 t1 v2 t2 m.

Definition sem_or_fp (v1:val) (t1:type) (v2: val) (t2:type) (m: mem) : option footprint :=
  sem_binarith_fp
    (fun sg n1 n2 => Some(Vint(Int.or n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.or n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 t1 v2 t2 m.


Definition sem_xor_fp (v1:val) (t1:type) (v2: val) (t2:type) (m: mem) : option footprint :=
  sem_binarith_fp
    (fun sg n1 n2 => Some(Vint(Int.xor n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.xor n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 t1 v2 t2 m.


(** *** Comparisons *)

Definition cmp_ptr_fp (m: mem) (c: comparison) (v1 v2: val) : option footprint :=
  if Archi.ptr64 then cmplu_bool_fp m c v1 v2
  else cmpu_bool_fp m c v1 v2.

Definition sem_cmp_fp (c:comparison)
           (v1: val) (t1: type) (v2: val) (t2: type) (m: mem) : option footprint :=
  match classify_cmp t1 t2 with
  | cmp_case_pp => cmp_ptr_fp m c v1 v2
  | cmp_case_pi si =>
    match v2 with
    | Vint n2 => let v2' := Vptrofs (ptrofs_of_int si n2) in cmp_ptr_fp m c v1 v2'
    | Vptr _ _ => if Archi.ptr64 then None else cmp_ptr_fp m c v1 v2
    | _ => None
    end
  | cmp_case_ip si =>
    match v1 with
    | Vint n1 => let v1' := Vptrofs (ptrofs_of_int si n1) in cmp_ptr_fp m c v1' v2
    | Vptr _ _ => if Archi.ptr64 then None else cmp_ptr_fp m c v1 v2
    | _ => None
    end
  | cmp_case_pl =>
    match v2 with
    | Vlong n2 => let v2' := Vptrofs (Ptrofs.of_int64 n2) in cmp_ptr_fp m c v1 v2'
    | Vptr _ _ => if Archi.ptr64 then cmp_ptr_fp m c v1 v2 else None
    | _ => None
    end
  | cmp_case_lp =>
    match v1 with
    | Vlong n1 => let v1' := Vptrofs (Ptrofs.of_int64 n1) in cmp_ptr_fp m c v1' v2
    | Vptr _ _ => if Archi.ptr64 then cmp_ptr_fp m c v1 v2 else None
    | _ => None
    end
  | cmp_default =>
    sem_binarith_fp
      (fun sg n1 n2 =>
         Some(Val.of_bool(match sg with Signed => Int.cmp c n1 n2 | Unsigned => Int.cmpu c n1 n2 end)))
      (fun sg n1 n2 =>
         Some(Val.of_bool(match sg with Signed => Int64.cmp c n1 n2 | Unsigned => Int64.cmpu c n1 n2 end)))
      (fun n1 n2 =>
         Some(Val.of_bool(Float.cmp c n1 n2)))
      (fun n1 n2 =>
         Some(Val.of_bool(Float32.cmp c n1 n2)))
      v1 t1 v2 t2 m
  end.

Lemma sem_cmp_sem_cmp_fp:
  forall c v1 t1 v2 t2 m v,
    sem_cmp c v1 t1 v2 t2 m = Some v ->
    exists fp, sem_cmp_fp c v1 t1 v2 t2 m = Some fp.
Proof.
  unfold sem_cmp, sem_cmp_fp, cmp_ptr, cmp_ptr_fp, option_map; intros.
  destruct classify_cmp;
  repeat match goal with
         | |- context[if ?x then _ else _] => destruct x eqn:?
         | |- context[match ?x with _ => _ end] => destruct x eqn:?
         | H: match ?x with _ => _ end = Some _ |- _ => destruct x eqn:?
         end;
  try discriminate;
  try (eapply cmpu_bool_cmpu_bool_fp; eauto).
  eapply sem_binarith_sem_binarith_fp; eauto.
Qed.


(** * Combined semantics of unary and binary operators *)
Definition sem_unary_operation_fp
           (op: unary_operation) (v: val) (ty: type) (m: mem) : option footprint:=
  match op with
  | Onotbool => sem_notbool_fp v ty m
  | Onotint => if sem_notint v ty then Some empfp else None
  | Oneg => if sem_neg v ty then Some empfp else None
  | Oabsfloat => if sem_absfloat v ty then Some empfp else None
  end.

Lemma sem_unary_operation_sem_unary_operation_fp:
  forall op v ty m v',
    sem_unary_operation op v ty m = Some v' ->
    exists fp, sem_unary_operation_fp op v ty m = Some fp.
Proof.
  unfold sem_unary_operation, sem_unary_operation_fp; intros.
  destruct op;
    try match goal with
          |- context[if ?x then _ else _] => destruct x; [eauto|discriminate]
        end.
  eapply sem_notbool_sem_notbool_fp; eauto.
Qed.

Lemma sem_unary_operation_fp_sem_unary_operation:
  forall op v ty m fp,
    sem_unary_operation_fp op v ty m = Some fp ->
    (exists v', sem_unary_operation op v ty m = Some v')
    \/ (op = Onotbool /\
       exists (b : block) (ofs : ptrofs),
         v = Vptr b ofs /\ Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) = false).
Proof.
  unfold sem_unary_operation, sem_unary_operation_fp; intros.
  destruct op;
    try match goal with
          H : context[if ?x then _ else _] |- _ => destruct x; [eauto|discriminate]
        end.
  eapply sem_notbool_fp_sem_notbool in H; destruct H; eauto.
Qed.

Definition sem_binary_operation_fp
           (cenv: composite_env)
           (op: binary_operation)
           (v1: val) (t1: type) (v2: val) (t2:type)
           (m: mem) : option footprint :=
  match op with
  | Oadd => sem_add_fp cenv v1 t1 v2 t2 m
  | Osub => sem_sub_fp cenv v1 t1 v2 t2 m
  | Omul => sem_mul_fp v1 t1 v2 t2 m
  | Omod => sem_mod_fp v1 t1 v2 t2 m
  | Odiv => sem_div_fp v1 t1 v2 t2 m
  | Oand => sem_and_fp v1 t1 v2 t2 m
  | Oor  => sem_or_fp v1 t1 v2 t2 m
  | Oxor => sem_xor_fp v1 t1 v2 t2 m
  | Oshl => if sem_shl v1 t1 v2 t2 then Some empfp else None
  | Oshr => if sem_shr v1 t1 v2 t2 then Some empfp else None
  | Oeq => sem_cmp_fp Ceq v1 t1 v2 t2 m
  | One => sem_cmp_fp Cne v1 t1 v2 t2 m
  | Olt => sem_cmp_fp Clt v1 t1 v2 t2 m
  | Ogt => sem_cmp_fp Cgt v1 t1 v2 t2 m
  | Ole => sem_cmp_fp Cle v1 t1 v2 t2 m
  | Oge => sem_cmp_fp Cge v1 t1 v2 t2 m
  end.

Lemma sem_binary_operation_sem_binary_operation_fp:
  forall cenv op v1 t1 v2 t2 m v,
    sem_binary_operation cenv op v1 t1 v2 t2 m = Some v ->
    exists fp, sem_binary_operation_fp cenv op v1 t1 v2 t2 m = Some fp.
Proof.
  unfold sem_binary_operation, sem_binary_operation_fp; intros.
  destruct op;
    try eapply sem_binarith_sem_binarith_fp; eauto;
      try eapply sem_cmp_sem_cmp_fp; eauto;
        try eapply sem_add_sem_add_fp; eauto;
          try eapply sem_sub_sem_sub_fp; eauto.
  destruct sem_shl; [eauto|discriminate].
  destruct sem_shr; [eauto|discriminate].
Qed.


Definition sem_incrdecr_fp
           (cenv: composite_env)
           (id: incr_or_decr) (v: val) (ty: type)
           (m: mem) : option footprint :=
  match id with
  | Incr => sem_add_fp cenv v ty (Vint Int.one) type_int32s m
  | Decr => sem_sub_fp cenv v ty (Vint Int.one) type_int32s m
  end.

Lemma sem_incrdecr_sem_incrdecr_fp:
  forall cenv id v ty m v',
    sem_incrdecr cenv id v ty m = Some v' ->
    exists fp, sem_incrdecr_fp cenv id v ty m = Some fp.
Proof.
  unfold sem_incrdecr, sem_incrdecr_fp; intros.
  destruct id;
    [ eapply sem_add_sem_add_fp | eapply sem_sub_sem_sub_fp ]; eauto.
Qed.