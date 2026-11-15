(* Statement-only formalization of VERINA corpus artifact verina_advanced_70,
   catalog title "semiOrderedPermutation": an executable computation of the
   minimum adjacent swaps needed to move 1 to the front and the list length
   to the back of an integer permutation, together with its positional
   correctness contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Fixpoint semiOrderedPermutation_idxOf
    (value : Z) (nums : list Z) : nat :=
  match nums with
  | [] => 0%nat
  | x :: xs =>
      if Z.eqb x value
      then 0%nat
      else S (semiOrderedPermutation_idxOf value xs)
  end.

Definition semiOrderedPermutation_precond
    (nums : list Z) : Prop :=
  let n := length nums in
  Nat.lt 0 n /\
  NoDup nums /\
  forallb
    (fun x =>
      andb
        (Z.leb 1 x)
        (Z.leb x (Z.of_nat n)))
    nums = true.

Definition semiOrderedPermutation
    (nums : list Z)
    (_h_precond : semiOrderedPermutation_precond nums) : Z :=
  let lengthList := length nums in
  let numOne := 1%Z in
  let largestNum := Z.of_nat lengthList in
  let firstIndex :=
    semiOrderedPermutation_idxOf numOne nums in
  let lastIndex :=
    semiOrderedPermutation_idxOf largestNum nums in
  let startPosition := 0%nat in
  let endPosition := Nat.sub lengthList 1%nat in
  let shouldMoveOne :=
    negb (Nat.eqb firstIndex startPosition) in
  let shouldMoveLast :=
    negb (Nat.eqb lastIndex endPosition) in
  let distanceOne :=
    if shouldMoveOne then firstIndex else 0%nat in
  let distanceLast :=
    if shouldMoveLast
    then Nat.sub endPosition lastIndex
    else 0%nat in
  let totalMoves := Nat.add distanceOne distanceLast in
  let needAdjustment := Nat.ltb lastIndex firstIndex in
  let adjustedMoves :=
    if needAdjustment
    then Nat.sub totalMoves 1%nat
    else totalMoves in
  Z.of_nat adjustedMoves.

Definition semiOrderedPermutation_postcond
    (nums : list Z)
    (result : Z)
    (_h_precond : semiOrderedPermutation_precond nums) : Prop :=
  let n := length nums in
  let pos1 :=
    semiOrderedPermutation_idxOf 1%Z nums in
  let posn :=
    semiOrderedPermutation_idxOf (Z.of_nat n) nums in
  if Nat.ltb posn pos1
  then
    Z.of_nat (Nat.add pos1 n) =
      Z.add (Z.add result 2%Z) (Z.of_nat posn)
  else
    Z.of_nat (Nat.add pos1 n) =
      Z.add (Z.add result 1%Z) (Z.of_nat posn).

Theorem semiOrderedPermutation_spec_satisfied
    (nums : list Z)
    (h_precond : semiOrderedPermutation_precond nums) :
  semiOrderedPermutation_postcond
    nums
    (semiOrderedPermutation nums h_precond)
    h_precond.
Admitted.
