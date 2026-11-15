(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_74,
  catalog title "solution": the executable program sums, over all nonempty
  contiguous subarrays of a natural-number list, the squares of their distinct
  element counts and satisfies the stated constrained-input expected-sum
  contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory pred_setTheory;

val solution_precond_def = new_definition (
  "solution_precond_def",
  ``solution_precond (nums : num list) <=>
      1 <= LENGTH nums /\
      LENGTH nums <= 100 /\
      EVERY (\x : num. 1 <= x /\ x <= 100) nums``
);

val solution_subarray_def = new_definition (
  "solution_subarray_def",
  ``solution_subarray
      (nums : num list) (i : num) (j : num) =
      TAKE (j - i + 1) (DROP i nums)``
);

val solution_distinctCount_def = new_definition (
  "solution_distinctCount_def",
  ``solution_distinctCount (l : num list) =
      CARD
        (FOLDL
          (\seen : num set. \x : num. x INSERT seen)
          ({} : num set)
          l)``
);

val solution_innerSum_def = new_definition (
  "solution_innerSum_def",
  ``solution_innerSum
      (nums : num list) (n : num) (i : num) =
      FOLDL
        (\acc : num. \d : num.
          let subarr = solution_subarray nums i (i + d) in
          let count = solution_distinctCount subarr in
            acc + count * count)
        0
        (COUNT_LIST (n - i))``
);

val solution_def = new_definition (
  "solution_def",
  ``solution (nums : num list) =
      let n = LENGTH nums in
        FOLDL
          (\acc : num. \i : num.
            acc + solution_innerSum nums n i)
          0
          (COUNT_LIST n)``
);

val solution_postDistinctCount_def = new_definition (
  "solution_postDistinctCount_def",
  ``solution_postDistinctCount (l : num list) =
      LENGTH
        (FOLDL
          (\seen : num list. \x : num.
            if MEM x seen then seen else x::seen)
          ([] : num list)
          l)``
);

val solution_expectedInnerSum_def = new_definition (
  "solution_expectedInnerSum_def",
  ``solution_expectedInnerSum
      (nums : num list) (n : num) (i : num) =
      FOLDL
        (\currentInnerSum : num. \d : num.
          let j = i + d in
          let subarr =
            TAKE (j - i + 1) (DROP i nums)
          in
          let count = solution_postDistinctCount subarr in
            currentInnerSum + count * count)
        0
        (COUNT_LIST (n - i))``
);

val solution_expectedSum_def = new_definition (
  "solution_expectedSum_def",
  ``solution_expectedSum (nums : num list) =
      let n = LENGTH nums in
        FOLDL
          (\outerSum : num. \i : num.
            outerSum + solution_expectedInnerSum nums n i)
          0
          (COUNT_LIST n)``
);

val solution_postcond_def = new_definition (
  "solution_postcond_def",
  ``solution_postcond
      (nums : num list) (result : num) <=>
      solution_precond nums ==>
      0 <= result /\
      result = solution_expectedSum nums``
);

val solution_spec_satisfied =
  ``!nums : num list.
      solution_postcond nums (solution nums)``;
