Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Ctypes.

Require Import Cop.

Require Import Footprint FMemory FMemOpFP.
Require Import FCop.

(** why make them local ... 
 move to Footprint.v ?*)
Local Notation locset := Locs.t.
Local Notation empls := Locs.emp.
Local Notation footprint := FP.t.
Local Notation empfp := FP.emp.
Local Notation FP := FP.Build_t.


Definition of_optfp (ofp: option footprint) : footprint :=
  match ofp with
  | Some fp => fp
  | None => empfp
  end.

(** Instrument C operations with footprints *)
(** * Semantic with memory read/writes *)

(** Footprint of cast: 
    when v is a pointer value under architecture, and casting to a bool value,
    we need to check the validity of the pointer, thus has weak_valid_pointer fp
    
    Note: for operation that would not return a value (i.e. return None),
    the footprint calculation returns None, instead of Some empfp.
 *)
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

Lemma sem_cast_fp_mapped:
  forall f m tm v tv ty ty' v' fp,
    Mem.inject f m tm ->
    Val.inject f v tv ->
    sem_cast v ty ty' m = Some v' -> 
    sem_cast_fp v ty ty' m = Some fp ->
    exists tfp, sem_cast_fp tv ty ty' tm = Some tfp /\
           fp_mapped f fp tfp.
Proof.
  clear. intros until fp. intros MEMINJ VALINJ CAST CAST_FP.
  destruct v; inv VALINJ;
    unfold sem_cast, sem_cast_fp in *;
    repeat
      (match goal with
       | H: match ?x with _ => _ end = _ |- _ => destruct x eqn:?
       | H: if ?x then _ else _ = _ |- _ => destruct x eqn:?
       end; try discriminate );
    try (exists empfp; split; [auto|apply emp_fp_mapped]; fail).
  eexists; split; [eauto|].
  inv CAST_FP.
  eapply weak_valid_inj_fp_mapped; eauto.
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

Lemma bool_val_fp_mapped:
  forall f m m' v ty b fp tv,
    bool_val v ty m = Some b ->
    bool_val_fp v ty m = Some fp ->
    Val.inject f v tv -> Mem.inject f m m' ->
    exists tfp, bool_val_fp tv ty m' = Some tfp /\ fp_mapped f fp tfp.
Proof.
  clear. intros.
  unfold bool_val_fp, bool_val in *.
  destruct classify_bool; inv H1; try discriminate;
    try (inv H0; eexists; split; [eauto|apply emp_fp_mapped]; fail).
  destruct Archi.ptr64; inv H0.
  match goal with H: context[if ?x then _ else _] |- _ => destruct x eqn:?; inv H end.
  eexists; split; [eauto|].
  eapply weak_valid_inj_fp_mapped; eauto.
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

Lemma sem_binarith_fp_mapped:
  forall f m tm v1 tv1 v2 tv2 ty1 ty2 sem1 sem2 sem3 sem4 v fp,
    Mem.inject f m tm ->
    Val.inject f v1 tv1 ->
    Val.inject f v2 tv2 ->
    (forall (sg : signedness) (n1 n2 : int), optval_self_injects (sem1 sg n1 n2)) ->
    (forall (sg : signedness) (n1 n2 : int64), optval_self_injects (sem2 sg n1 n2)) ->
    (forall n1 n2 : float, optval_self_injects (sem3 n1 n2)) ->
    (forall n1 n2 : float32, optval_self_injects (sem4 n1 n2)) ->
    sem_binarith sem1 sem2 sem3 sem4 v1 ty1 v2 ty2 m = Some v ->
    sem_binarith_fp sem1 sem2 sem3 sem4 v1 ty1 v2 ty2 m = Some fp ->
    exists tfp, sem_binarith_fp sem1 sem2 sem3 sem4 tv1 ty1 tv2 ty2 tm = Some tfp /\
           fp_mapped f fp tfp.
Proof.
  intros until fp. intros MEMINJ VALINJ1 VALINJ2 SEM1 SEM2 SEM3 SEM4 BINARITH BINARITHFP.
  exploit sem_binarith_inject; eauto.
  
  instantiate (1:=tm). intros.
  exploit Mem.weak_valid_pointer_inject_no_overflow; eauto. intro.
  unfold Ptrofs.add. rewrite Ptrofs.unsigned_repr; auto.
  exploit Mem.weak_valid_pointer_inject; eauto. intro.
  rewrite Ptrofs.unsigned_repr; eauto.
  exploit Mem.mi_representable; eauto.
  rewrite Mem.weak_valid_pointer_spec, Mem.valid_pointer_nonempty_perm, Mem.valid_pointer_nonempty_perm in H0.
  instantiate (1:=ofs). generalize H0; clear. intro H. destruct H as [H|H]; apply Mem.perm_cur_max in H; auto.
  intros [DELTA OFS]. split. Lia.lia. generalize OFS. clear. destruct ofs. intros. simpl in *. Lia.lia.
  intros [tv [TBINARITH TVALINJ]].
  
  unfold sem_binarith, sem_binarith_fp in *.
  destruct (sem_cast v1 ty1 _ _) eqn:? ;
    try destruct (sem_cast v2 ty2 _ _) eqn:? ; try discriminate;
      destruct (sem_cast tv1 ty1 _ _) eqn:? ;
      try destruct (sem_cast tv2 ty2 _ _) eqn:? ; try discriminate;
        destruct classify_binarith eqn:? ; try discriminate;
          destruct v0, v3; try discriminate;
            destruct v4, v5; try discriminate;
              destruct (sem_cast_fp v1 _ _) eqn:? ; try discriminate;
                destruct (sem_cast_fp v2 _ _) eqn:? ; try discriminate.
  
  exploit sem_cast_fp_mapped. exact MEMINJ. exact VALINJ1. eauto. eauto. intros [tt [CASTFP1 MAPPED1]].
  exploit sem_cast_fp_mapped. exact MEMINJ. exact VALINJ2. eauto. eauto. intros [tt0 [CASTFP2 MAPPED2]].
  rewrite BINARITH in BINARITHFP; inv BINARITHFP. rewrite CASTFP1, CASTFP2, TBINARITH.
  eexists; split; [eauto|apply fp_mapped_union; auto].
  
  exploit sem_cast_fp_mapped. exact MEMINJ. exact VALINJ1. eauto. eauto. intros [tt [CASTFP1 MAPPED1]].
  exploit sem_cast_fp_mapped. exact MEMINJ. exact VALINJ2. eauto. eauto. intros [tt0 [CASTFP2 MAPPED2]].
  rewrite BINARITH in BINARITHFP; inv BINARITHFP. rewrite CASTFP1, CASTFP2, TBINARITH.
  eexists; split; [eauto|apply fp_mapped_union; auto].
  
  exploit sem_cast_fp_mapped. exact MEMINJ. exact VALINJ1. eauto. eauto. intros [tt [CASTFP1 MAPPED1]].
  exploit sem_cast_fp_mapped. exact MEMINJ. exact VALINJ2. eauto. eauto. intros [tt0 [CASTFP2 MAPPED2]].
  rewrite BINARITH in BINARITHFP; inv BINARITHFP. rewrite CASTFP1, CASTFP2, TBINARITH.
  eexists; split; [eauto|apply fp_mapped_union; auto].
  
  exploit sem_cast_fp_mapped. exact MEMINJ. exact VALINJ1. eauto. eauto. intros [tt [CASTFP1 MAPPED1]].
  exploit sem_cast_fp_mapped. exact MEMINJ. exact VALINJ2. eauto. eauto. intros [tt0 [CASTFP2 MAPPED2]].
  rewrite BINARITH in BINARITHFP; inv BINARITHFP. rewrite CASTFP1, CASTFP2, TBINARITH.
  eexists; split; [eauto|apply fp_mapped_union; auto]. 
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
  | _, _ => empfp
  end.

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

Lemma compu_bool_fp_inject_mapped:
      forall f m tm v1 tv1 v2 tv2 c v fp,
        Mem.inject f m tm ->
        Val.inject f v1 tv1 ->
        Val.inject f v2 tv2 ->
        Val.cmpu_bool (Mem.valid_pointer m) c v1 v2 = Some v ->
        cmpu_bool_fp m c v1 v2 = Some fp ->
        exists tfp, cmpu_bool_fp tm c tv1 tv2 = Some tfp /\ fp_mapped f fp tfp.
Proof.
  intros until fp. intros MEMINJ VINJ1 VINJ2 CMP FP.
  unfold Val.cmpu_bool, cmpu_bool_fp in *.
  destruct v1; inv VINJ1; try discriminate;
    destruct v2; inv VINJ2; try discriminate;
      try (eexists; split; [eauto|eapply emp_fp_mapped]; fail);
      destruct Archi.ptr64; try discriminate;
        try (clear; eexists; split; [eauto|eapply emp_fp_mapped]; fail).
  
  destruct Int.eq, Val.cmp_different_blocks; try discriminate. inv FP.
  eexists; split; eauto. eapply weak_valid_inj_fp_mapped; eauto.
  unfold Mem.weak_valid_pointer. simpl in CMP.
  match goal with |- ?x = true => destruct x; try discriminate end; auto.

  destruct Int.eq, Val.cmp_different_blocks; try discriminate. inv FP.
  eexists; split; eauto. eapply weak_valid_inj_fp_mapped; eauto.
  unfold Mem.weak_valid_pointer. simpl in CMP.
  match goal with |- ?x = true => destruct x; try discriminate end; auto.

  destruct (eq_block b b0); subst.
  * rewrite H1 in H2; inv H2. inv FP. destruct eq_block; [|congruence]. eexists; split; eauto.
    apply fp_mapped_union; eapply weak_valid_inj_fp_mapped; eauto;
      unfold Mem.weak_valid_pointer; simpl in CMP; match goal with |- ?x = true => destruct x; try discriminate end; auto.
    rewrite andb_false_r in CMP. inv CMP.
  * destruct (eq_block b2 b3); subst.
    ** destruct Val.cmp_different_blocks; try discriminate. inv FP.
       eexists. split; eauto. unfold weak_valid_pointer_fp.
       match goal with 
         H: context[if ?x then _ else _] |- _ =>
         destruct x eqn:VALID; simpl in H; inv H
       end.
       rewrite andb_true_iff in VALID. destruct VALID as [VALID VALID0].
       exploit Mem.valid_pointer_inject; try eapply VALID; eauto.
       exploit Mem.valid_pointer_inject; try eapply VALID0; eauto.
       intros. unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr. rewrite H, H0.
       apply fp_mapped_union; unfold valid_pointer_fp;
         constructor; simpl; try apply emp_locs_mapped.
       constructor; intros.
       rewrite range_locset_loc in H3. inv H3.
       apply Loc_Mapped with b (tofs - delta) delta; [|auto|Lia.lia].
       apply range_locset_loc. intuition.
       constructor; intros.
       rewrite range_locset_loc in H3. inv H3.
       apply Loc_Mapped with b0 (tofs - delta0) delta0; [|auto|Lia.lia].
       apply range_locset_loc. intuition.

       1-3: clear VALID H1 H0 i. 4-6: clear VALID0 H2 H i0.
       1-6: (exploit Mem.valid_pointer_inject_no_overflow; eauto;
             exploit Mem.mi_representable; eauto;
             try rewrite Mem.valid_pointer_nonempty_perm in *; eauto with mem;
             intros; try destruct i0; try destruct i; simpl in *; try Lia.lia).

    ** destruct Val.cmp_different_blocks; try discriminate. inv FP.
       eexists. split; auto.
       match goal with 
         H: context[if ?x then _ else _] |- _ =>
         destruct x eqn:VALID; simpl in H; inv H
       end.
       rewrite andb_true_iff in VALID. destruct VALID.
       apply fp_mapped_union; eapply valid_pointer_inj_fp_mapped; eauto.
Qed.

(** This lemma is wierd. Interesting cases are discriminated because Archi.ptr64 = false *)
Lemma complu_bool_fp_inject_mapped:
  forall (f : meminj) (m tm : mem) (v1 tv1 v2 tv2 : val) (c : comparison) 
    (v : bool) (fp : footprint),
    Mem.inject f m tm ->
    Val.inject f v1 tv1 ->
    Val.inject f v2 tv2 ->
    Val.cmplu_bool (Mem.valid_pointer m) c v1 v2 = Some v ->
    cmplu_bool_fp m c v1 v2 = Some fp ->
    exists tfp : footprint, cmplu_bool_fp tm c tv1 tv2 = Some tfp /\ fp_mapped f fp tfp.
Proof.
  intros until fp. intros MEMINJ VINJ1 VINJ2 CMP FP.
  unfold Val.cmplu_bool, cmplu_bool_fp in *.
  destruct v1; inv VINJ1; try discriminate;
    destruct v2; inv VINJ2; try discriminate; 
      try (eexists; split; [eauto|eapply emp_fp_mapped]; fail);
      try (clear; eexists; split; [eauto|eapply emp_fp_mapped]; fail).
Qed.
  
Definition cmp_ptr_fp (m: mem) (c: comparison) (v1 v2: val) : option footprint :=
  if Archi.ptr64 then cmplu_bool_fp m c v1 v2
  else cmpu_bool_fp m c v1 v2.

(* END *)

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

(*
Lemma sem_cmp_fp_sem_cmp:
  forall c v1 t1 v2 t2 m fp,
    sem_cmp_fp c v1 t1 v2 t2 m = Some fp ->
    (exists v, sem_cmp c v1 t1 v2 t2 m = Some v)
    \/ ???
 *)

Ltac BRANCHES :=
  repeat match goal with
         | |- context[if ?x then _ else _] => destruct x eqn:?; subst; simpl in *; try discriminate
         | |- context[match ?x with _ => _ end] => destruct x eqn:?; subst; simpl in *; try discriminate
         | H: context[if ?x then _ else _] |- _ => destruct x eqn:?; subst; simpl in *; try discriminate
         | H: _ && _ = true |- _ => apply andb_true_iff in H; destruct H
         end.
Ltac BINARITH :=
  eapply sem_binarith_fp_mapped; eauto; clear; intros; unfold optval_self_injects, Val.of_bool; auto;
  repeat match goal with
         | |- context[if ?x then _ else _] => destruct x eqn:?; auto
         | |- context[match ?x with _ => _ end] => destruct x eqn:?; auto
         end; 
  try discriminate.

Lemma sem_cmp_inj_fp_mapped:
  forall f m tm v1 tv1 v2 tv2 ty1 ty2 c v fp,
    Mem.inject f m tm ->
    Val.inject f v1 tv1 ->
    Val.inject f v2 tv2 ->
    sem_cmp c v1 ty1 v2 ty2 m = Some v ->
    sem_cmp_fp c v1 ty1 v2 ty2 m = Some fp ->
    exists tfp : footprint, sem_cmp_fp c tv1 ty1 tv2 ty2 tm = Some tfp /\ fp_mapped f fp tfp.
Proof.
  intros until fp.
  intros MEMINJ VALINJ1 VALINJ2 CMP CMPFP.
  destruct Archi.ptr64 eqn:PTR64; try discriminate.
  unfold sem_cmp, sem_cmp_fp, cmp_ptr, cmp_ptr_fp, Val.cmpu_bool, cmpu_bool_fp, Vptrofs in *; try rewrite PTR64 in *.
  destruct (classify_cmp ty1 ty2); try discriminate;
    match goal with
    | |- context[sem_binarith_fp] => BINARITH
    | _ =>
      destruct v1; inv VALINJ1; try discriminate;
        destruct v2; inv VALINJ2; try discriminate;
          try (clear; eexists; split; [eauto|eapply emp_fp_mapped]; fail);
          BRANCHES; try congruence; inv CMPFP;
            (eexists; split; [eauto|try eapply emp_fp_mapped]);
            try match goal with
                | |- context[fp_mapped _ (FP.union _ _) _] => apply fp_mapped_union
                end;
            try (eapply weak_valid_inj_fp_mapped; eauto);
            try (eapply weak_valid_inj_valid_fp_mapped; eauto);
            try (eapply valid_inj_weak_valid_fp_mapped; eauto);
            try (eapply valid_pointer_inj_fp_mapped; eauto)
    end.
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

Lemma sem_unary_operation_fp_mapped:
  forall f m tm v tv op ty v' fp,
    Mem.inject f m tm ->
    Val.inject f v tv ->
    sem_unary_operation op v ty m = Some v' ->
    sem_unary_operation_fp op v ty m = Some fp ->
    exists tfp, sem_unary_operation_fp op tv ty tm = Some tfp /\
           fp_mapped f fp tfp.
Proof.
  clear. intros until fp. intros MEMINJ VALINJ COP OPFP.
  unfold sem_unary_operation_fp, sem_unary_operation in *. 
  destruct op; try (exists empfp; split; [auto|apply emp_fp_mapped]; fail).
  * unfold sem_notbool, bool_val, sem_notbool_fp, bool_val_fp in *.
    destruct (classify_bool ty); destruct v; simpl in *; try congruence;
      inv VALINJ; try (exists empfp; split; [auto|apply emp_fp_mapped]; fail);
        destruct Archi.ptr64; simpl in *; try congruence;
          eexists; (split; [eauto|]); destruct Mem.weak_valid_pointer eqn:? ;
            inv COP; inv OPFP;
              eapply weak_valid_inj_fp_mapped; eauto.
    
  * rewrite COP in OPFP. inv OPFP.
    exists empfp. unfold sem_notint in *.
    destruct classify_notint eqn:?; simpl in COP; try discriminate;
      destruct v; try discriminate; inv VALINJ;
        (split; [eauto|apply emp_fp_mapped]).
  * rewrite COP in OPFP. inv OPFP.
    exists empfp. unfold sem_neg in *.
    destruct classify_neg eqn:?; simpl in COP; try discriminate;
      destruct v; try discriminate; inv VALINJ;
        (split; [eauto|apply emp_fp_mapped]).
  * rewrite COP in OPFP. inv OPFP.
    exists empfp. unfold sem_absfloat in *.
    destruct classify_neg eqn:?; simpl in COP; try discriminate;
      destruct v; try discriminate; inv VALINJ;
        (split; [eauto|apply emp_fp_mapped]).
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


Lemma sem_binary_operation_fp_mapped:
  forall f m tm v1 tv1 v2 tv2 cenv op ty1 ty2 v fp,
    Mem.inject f m tm ->
    Val.inject f v1 tv1 ->
    Val.inject f v2 tv2 ->
    sem_binary_operation cenv op v1 ty1 v2 ty2 m = Some v ->
    sem_binary_operation_fp cenv op v1 ty1 v2 ty2 m = Some fp ->
    exists tfp, sem_binary_operation_fp cenv op tv1 ty1 tv2 ty2 tm = Some tfp
           /\ fp_mapped f fp tfp.
Proof.
  clear. intros until fp.
  intros MEMINJ VALINJ1 VALINJ2 BINOP BINOPFP.
  destruct Archi.ptr64 eqn:PTR64; try discriminate.
  unfold sem_binary_operation, sem_binary_operation_fp in *; destruct op.

  1-8: unfold sem_add, sem_add_fp, sem_sub, sem_sub_fp, sem_mul, sem_mul_fp, sem_div, sem_div_fp,
       sem_mod, sem_mod_fp, sem_and, sem_and_fp, sem_or, sem_or_fp, sem_xor, sem_xor_fp, sem_shl, sem_shr,
       sem_cmp, sem_cmp_fp, cmp_ptr, cmp_ptr_fp, Val.cmpu_bool, cmpu_bool_fp, Vptrofs in *.

  destruct classify_add; 
    try match goal with
        | |- context[sem_binarith_fp] => BINARITH
        | _ => BRANCHES 
        end;
    try (exists empfp; split; [auto|apply emp_fp_mapped]);
    try (inv VALINJ1; inv VALINJ2; simpl in *; discriminate).

  destruct classify_sub; 
    try match goal with
        | |- context[sem_binarith_fp] => BINARITH
        | _ => rewrite PTR64 in *;
                inv VALINJ1; inv VALINJ2; simpl in *; try discriminate;
                  try (exists empfp; split; [auto|apply emp_fp_mapped]);
                  BRANCHES; try congruence
        end.

  1-6: BINARITH.
  1-2: unfold sem_shl, sem_shr, sem_shift in *;
    destruct classify_shift;
    destruct v1, v2; try discriminate;
      inv VALINJ1; inv VALINJ2;
        match goal with
        | |- context[if Int.ltu _ _ then _ else _] => destruct Int.ltu; try discriminate
        | |- context[if Int64.ltu _ _ then _ else _] => destruct Int64.ltu; try discriminate
        end;
        (clear; eexists; split; [eauto|eapply emp_fp_mapped]).
  1-6: eapply sem_cmp_inj_fp_mapped; eauto.
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