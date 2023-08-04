Require Import Values.

Module Type BSET.
  Parameter t : Type.
  Parameter emp: t.
  Parameter subset : t -> t -> Prop.
  Axiom emp_subset: forall bs: t, subset emp bs.
  Parameter belongsto : t -> block -> Prop.
(*  Parameter belongstob : t -> block -> bool. *)
  
  Parameter inj : Type.
  Parameter inj_emp: inj.
  Parameter inj_id: inj.
  Parameter inj_subset: inj -> inj -> Prop.
  Parameter inj_comp: inj -> inj -> inj.
  Axiom inj_subset_refl: forall f:inj, inj_subset f f.
  
  Parameter inject : inj -> t -> t -> Prop.
  Parameter inject_block: inj -> block -> block -> Prop.

  Parameter inj_to_meminj: inj -> meminj.
End BSET.


Module Bset <: BSET.
  Definition t := block -> Prop.
  Definition emp : t := fun _ => False.
  Definition subset (bs1 bs2: t) :=
    forall b, bs1 b -> bs2 b.
  Theorem emp_subset: forall bs, subset emp bs.
  Proof. firstorder. Qed.
  Definition belongsto (bs: t) (b: block) : Prop := bs b.
  Definition inj:= block -> option block.
  Definition inj_emp : inj := fun _ => None.
  Definition inj_id : inj := fun b => Some b.
  Definition inj_subset (j1 j2: inj) : Prop :=
    forall b b', j1 b = Some b' -> j2 b = Some b'.
  Definition inj_comp (j1 j2: inj) : inj :=
    fun b =>
      match j1 b with
      | Some b' => Some b'
      | None => match j2 b with
                | Some b' => Some b'
                | None => None
                end
      end.
  Theorem inj_subset_refl: forall j:inj, inj_subset j j.
  Proof. firstorder. Qed.

  Definition inj_inject (j: inj) :=
    forall b1 b2 b', j b1 = Some b' -> j b2 = Some b' -> b1 = b2.
  
  Record inject_weak' (j: inj) (bs1 bs2: t) :=
    {
      inj_dom': forall b b', j b = Some b' -> belongsto bs1 b;
      inj_range: forall b', belongsto bs2 b' -> exists b, j b = Some b';
      inj_range': forall b b', j b = Some b' -> belongsto bs2 b';
      inj_injective: forall b1 b2 b',
          j b1 = Some b' ->
          j b2 = Some b' ->
          b1 = b2;
    }.
  Definition inject_weak := inject_weak'.
  
  Record inject' (j: inj) (bs1 bs2: t) :=
    {
      inj_weak: inject_weak' j bs1 bs2;
      inj_dom: forall b, belongsto bs1 b -> exists b', j b = Some b';
    }.
  Definition inject := inject'.
  
  
  Definition inject_block (j: inj) (b b': block) : Prop := j b = Some b'.
  Definition inj_to_meminj (j: inj) : meminj :=
    fun b => match j b with
             | Some b' => Some (b', BinNums.Z0)
             | None => None
             end.
End Bset.


