(*
  Statement-only formalization of VERINA corpus artifact verina_basic_7,
  catalog title "sumOfSquaresOfFirstNOddNumbers": the executable
  natural-number recursion sums the squares of the first n odd numbers and
  satisfies the stated closed-form contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val sumOfSquaresOfFirstNOddNumbers_precond_def = new_definition (
  "sumOfSquaresOfFirstNOddNumbers_precond_def",
  ``sumOfSquaresOfFirstNOddNumbers_precond (n : num) <=> T``
);

val sumOfSquaresOfFirstNOddNumbers_loop_def = Define `
  (sumOfSquaresOfFirstNOddNumbers_loop
      0 (sum : num) =
     sum) /\
  (sumOfSquaresOfFirstNOddNumbers_loop
      (SUC k) sum =
     sumOfSquaresOfFirstNOddNumbers_loop
       k
       (sum +
        (2 * SUC k - 1) * (2 * SUC k - 1)))
`;

val sumOfSquaresOfFirstNOddNumbers_def = new_definition (
  "sumOfSquaresOfFirstNOddNumbers_def",
  ``sumOfSquaresOfFirstNOddNumbers (n : num) =
      sumOfSquaresOfFirstNOddNumbers_loop n 0``
);

val sumOfSquaresOfFirstNOddNumbers_postcond_def = new_definition (
  "sumOfSquaresOfFirstNOddNumbers_postcond_def",
  ``sumOfSquaresOfFirstNOddNumbers_postcond
      (n : num) (result : num) <=>
      result - (n * (2 * n - 1) * (2 * n + 1) DIV 3) = 0 /\
      (n * (2 * n - 1) * (2 * n + 1) DIV 3) - result = 0``
);

val sumOfSquaresOfFirstNOddNumbers_spec_satisfied =
  ``!n : num.
      sumOfSquaresOfFirstNOddNumbers_precond n ==>
      sumOfSquaresOfFirstNOddNumbers_postcond
        n (sumOfSquaresOfFirstNOddNumbers n)``;
