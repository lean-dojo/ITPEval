(*
  Statement-only formalization of VERINA corpus artifact verina_basic_65,
  catalog title "SquareRoot": the fuel-bounded executable natural-number
  program computes the integer square root by incrementing a candidate while
  its successor square is at most N, under the total precondition and stated
  correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val SquareRoot_precond_def = new_definition (
  "SquareRoot_precond_def",
  ``SquareRoot_precond (N : num) <=> T``
);

val SquareRoot_boundedLoop_def = Define `
  (SquareRoot_boundedLoop
      0 (N : num) (r : num) =
     r) /\
  (SquareRoot_boundedLoop
      (SUC bound) N r =
     if (r + 1) * (r + 1) <= N then
       SquareRoot_boundedLoop bound N (r + 1)
     else
       r)
`;

val SquareRoot_def = new_definition (
  "SquareRoot_def",
  ``SquareRoot (N : num) =
      SquareRoot_boundedLoop (N + 1) N 0``
);

val SquareRoot_postcond_def = new_definition (
  "SquareRoot_postcond_def",
  ``SquareRoot_postcond
      (N : num) (result : num) <=>
      result * result <= N /\
      N < (result + 1) * (result + 1)``
);

val SquareRoot_spec_satisfied =
  ``!N : num.
      SquareRoot_precond N ==>
      SquareRoot_postcond N (SquareRoot N)``;
