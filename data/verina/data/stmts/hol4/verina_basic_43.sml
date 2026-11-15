(*
  Statement-only formalization of VERINA corpus artifact verina_basic_43,
  catalog title "sumOfFourthPowerOfOddNumbers": the executable recursive
  natural-number program sums the fourth powers of the first n odd numbers
  and satisfies the stated polynomial correctness contract. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val sumOfFourthPowerOfOddNumbers_precond_def = new_definition (
  "sumOfFourthPowerOfOddNumbers_precond_def",
  ``sumOfFourthPowerOfOddNumbers_precond (n : num) <=> T``
);

val sumOfFourthPowerOfOddNumbers_def = Define `
  (sumOfFourthPowerOfOddNumbers 0 = 0) /\
  (sumOfFourthPowerOfOddNumbers (SUC n) =
     sumOfFourthPowerOfOddNumbers n + (2 * n + 1) EXP 4)
`;

val sumOfFourthPowerOfOddNumbers_postcond_def = new_definition (
  "sumOfFourthPowerOfOddNumbers_postcond_def",
  ``sumOfFourthPowerOfOddNumbers_postcond
      (n : num) (result : num) <=>
      15 * result =
        n * (2 * n + 1) *
          (((7 + 24 * n EXP 3) - 12 * n EXP 2) - 14 * n)``
);

val sumOfFourthPowerOfOddNumbers_spec_satisfied =
  ``!n : num.
      sumOfFourthPowerOfOddNumbers_precond n ==>
      sumOfFourthPowerOfOddNumbers_postcond
        n (sumOfFourthPowerOfOddNumbers n)``;
