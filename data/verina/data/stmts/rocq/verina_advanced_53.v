(* Statement-only formalization of VERINA corpus artifact verina_advanced_53,
   catalog title "minimumRightShifts": an executable bounded search for the
   minimum number of cyclic right shifts that sorts a distinct integer list,
   together with its minimality and impossibility correctness contract. This
   file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Sorting.Sorted
  ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition minimumRightShifts_precond
    (nums : list Z) : Prop :=
  NoDup nums.

Fixpoint minimumRightShifts_isSortedAux
    (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: ((y :: xs) as tail) =>
      if Z.leb x y
      then minimumRightShifts_isSortedAux tail
      else false
  end.

Definition minimumRightShifts_rightShiftOnce
    (l : list Z) : list Z :=
  match rev l with
  | [] => []
  | last :: revInit => last :: rev revInit
  end.

Fixpoint minimumRightShifts_rightShift
    (k : nat)
    (l : list Z) : list Z :=
  match k with
  | O => l
  | S k' =>
      minimumRightShifts_rightShift
        k' (minimumRightShifts_rightShiftOnce l)
  end.

Fixpoint minimumRightShifts_checkShifts_fuel
    (fuel n shifts_count : nat)
    (current_list : list Z) : Z :=
  match fuel with
  | O => (-1)%Z
  | S fuel' =>
      if Nat.leb n shifts_count
      then (-1)%Z
      else if minimumRightShifts_isSortedAux current_list
      then Z.of_nat shifts_count
      else
        minimumRightShifts_checkShifts_fuel
          fuel' n (S shifts_count)
          (minimumRightShifts_rightShiftOnce current_list)
  end.

Definition minimumRightShifts_checkShifts
    (n shifts_count : nat)
    (current_list : list Z) : Z :=
  minimumRightShifts_checkShifts_fuel
    n n shifts_count current_list.

Definition minimumRightShifts
    (nums : list Z)
    (_h_precond : minimumRightShifts_precond nums) : Z :=
  let n := length nums in
  if Nat.leb n 1%nat
  then 0%Z
  else if minimumRightShifts_isSortedAux nums
  then 0%Z
  else
    minimumRightShifts_checkShifts
      n 1%nat (minimumRightShifts_rightShiftOnce nums).

Definition minimumRightShifts_isSorted
    (l : list Z) : Prop :=
  StronglySorted Z.le l.

Definition minimumRightShifts_allEarlierUnsorted
    (bound : nat)
    (nums : list Z) : Prop :=
  forall k : nat,
    (k < bound)%nat ->
    ~ minimumRightShifts_isSorted
        (minimumRightShifts_rightShift k nums).

Definition minimumRightShifts_postcond
    (nums : list Z)
    (result : Z)
    (_h_precond : minimumRightShifts_precond nums) : Prop :=
  let n := length nums in
  if Nat.leb n 1%nat
  then result = 0%Z
  else
    (0 <= result /\
     result < Z.of_nat n /\
     minimumRightShifts_isSorted
       (minimumRightShifts_rightShift (Z.to_nat result) nums) /\
     minimumRightShifts_allEarlierUnsorted
       (Z.to_nat result) nums) \/
    (result = (-1)%Z /\
     minimumRightShifts_allEarlierUnsorted n nums).

Theorem minimumRightShifts_spec_satisfied
    (nums : list Z)
    (h_precond : minimumRightShifts_precond nums) :
  minimumRightShifts_postcond
    nums
    (minimumRightShifts nums h_precond)
    h_precond.
Admitted.
