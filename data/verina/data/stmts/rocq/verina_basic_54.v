(* Statement-only formalization of VERINA corpus artifact verina_basic_54,
   catalog title "CanyonSearch": an executable two-pointer search for the
   minimum absolute difference between elements of two nonempty nondecreasing
   integer arrays, together with its correctness contract. This file contains
   no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Sorting.Sorted
  ZArith.

Import ListNotations.

Definition CanyonSearch_precond
    (a b : list Z) : Prop :=
  a <> [] /\
  b <> [] /\
  StronglySorted Z.le a /\
  StronglySorted Z.le b.

Fixpoint canyonSearchAux_fuel
    (fuel : nat)
    (a b : list Z)
    (m n d : nat) : nat :=
  match fuel with
  | O => d
  | S fuel' =>
      if andb (Nat.ltb m (length a)) (Nat.ltb n (length b))
      then
        let ai := nth m a 0%Z in
        let bi := nth n b 0%Z in
        let diff := Z.abs_nat (ai - bi)%Z in
        let new_d := if Nat.ltb diff d then diff else d in
        if Z.leb ai bi
        then canyonSearchAux_fuel fuel' a b (S m) n new_d
        else canyonSearchAux_fuel fuel' a b m (S n) new_d
      else d
  end.

Definition canyonSearchAux
    (a b : list Z)
    (m n d : nat) : nat :=
  canyonSearchAux_fuel
    (Nat.sub (Nat.sub (Nat.add (length a) (length b)) m) n)
    a b m n d.

Definition CanyonSearch
    (a b : list Z)
    (_h_precond : CanyonSearch_precond a b) : nat :=
  let a0 := nth 0%nat a 0%Z in
  let b0 := nth 0%nat b 0%Z in
  let init :=
    if Z.ltb a0 b0
    then Z.abs_nat (b0 - a0)%Z
    else Z.abs_nat (a0 - b0)%Z in
  canyonSearchAux a b 0%nat 0%nat init.

Definition CanyonSearch_postcond
    (a b : list Z)
    (result : nat)
    (_h_precond : CanyonSearch_precond a b) : Prop :=
  (exists ai bi : Z,
      In ai a /\
      In bi b /\
      result = Z.abs_nat (ai - bi)%Z) /\
  (forall ai bi : Z,
      In ai a ->
      In bi b ->
      Nat.le result (Z.abs_nat (ai - bi)%Z)).

Theorem CanyonSearch_spec_satisfied
    (a b : list Z)
    (h_precond : CanyonSearch_precond a b) :
  CanyonSearch_postcond
    a b (CanyonSearch a b h_precond) h_precond.
Admitted.
