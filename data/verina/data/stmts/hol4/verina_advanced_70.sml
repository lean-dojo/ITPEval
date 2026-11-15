(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_70,
  catalog title "semiOrderedPermutation": the executable program computes the
  minimum adjacent swaps needed to move 1 to the front and the list length to
  the back of a nonempty integer permutation. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val semiOrderedPermutation_idxOf_def = Define `
  (semiOrderedPermutation_idxOf
      (value : int) ([] : int list) = 0) /\
  (semiOrderedPermutation_idxOf
      value (head::tail) =
     if head = value then
       0
     else
       SUC (semiOrderedPermutation_idxOf value tail))
`;

val semiOrderedPermutation_precond_def = new_definition (
  "semiOrderedPermutation_precond_def",
  ``semiOrderedPermutation_precond (nums : int list) <=>
      0 < LENGTH nums /\
      ALL_DISTINCT nums /\
      EVERY
        (\x : int.
          1 <= x /\ x <= int_of_num (LENGTH nums))
        nums``
);

val semiOrderedPermutation_def = new_definition (
  "semiOrderedPermutation_def",
  ``semiOrderedPermutation (nums : int list) =
      let lengthList = LENGTH nums in
      let numOne = (1 : int) in
      let largestNum = int_of_num lengthList in
      let firstIndex =
        semiOrderedPermutation_idxOf numOne nums
      in
      let lastIndex =
        semiOrderedPermutation_idxOf largestNum nums
      in
      let startPosition = 0 in
      let endPosition = lengthList - 1 in
      let shouldMoveOne = firstIndex <> startPosition in
      let shouldMoveLast = lastIndex <> endPosition in
      let distanceOne =
        if shouldMoveOne then firstIndex else 0
      in
      let distanceLast =
        if shouldMoveLast then endPosition - lastIndex else 0
      in
      let totalMoves = distanceOne + distanceLast in
      let needAdjustment = firstIndex > lastIndex in
      let adjustedMoves =
        if needAdjustment then totalMoves - 1 else totalMoves
      in
        int_of_num adjustedMoves``
);

val semiOrderedPermutation_postcond_def = new_definition (
  "semiOrderedPermutation_postcond_def",
  ``semiOrderedPermutation_postcond
      (nums : int list) (result : int) <=>
      let n = LENGTH nums in
      let pos1 =
        semiOrderedPermutation_idxOf (1 : int) nums
      in
      let posn =
        semiOrderedPermutation_idxOf (int_of_num n) nums
      in
        if pos1 > posn then
          int_of_num (pos1 + n) =
            result + (2 : int) + int_of_num posn
        else
          int_of_num (pos1 + n) =
            result + (1 : int) + int_of_num posn``
);

val semiOrderedPermutation_spec_satisfied =
  ``!nums : int list.
      semiOrderedPermutation_precond nums ==>
      semiOrderedPermutation_postcond
        nums (semiOrderedPermutation nums)``;
