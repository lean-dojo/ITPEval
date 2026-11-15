(*
  Statement-only formalization of VERINA artifact verina_advanced_54,
  cataloged as "missingNumber": under the distinctness and range
  precondition, the executable triangular-sum calculation returns the unique
  natural number omitted from zero through the list length. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val missingNumber_precond_def = new_definition (
  "missingNumber_precond_def",
  ``missingNumber_precond (nums : num list) <=>
      EVERY (\x. x <= LENGTH nums) nums /\
      ALL_DISTINCT nums``
);

val missingNumber_def = new_definition (
  "missingNumber_def",
  ``missingNumber (nums : num list) =
      let n = LENGTH nums in
      let expectedSum = n * (n + 1) DIV 2 in
      let actualSum = FOLDL (\acc x. acc + x) 0 nums in
        expectedSum - actualSum``
);

val missingNumber_postcond_def = new_definition (
  "missingNumber_postcond_def",
  ``missingNumber_postcond
      (nums : num list) (result : num) <=>
      let n = LENGTH nums in
        MEM result (COUNT_LIST (n + 1)) /\
        ~MEM result nums /\
        !x : num.
          MEM x (COUNT_LIST (n + 1)) ==>
          x <> result ==>
          MEM x nums``
);

val missingNumber_spec_satisfied =
  ``!nums : num list.
      missingNumber_precond nums ==>
      missingNumber_postcond nums (missingNumber nums)``;
