(*
  Statement-only formalization of VERINA corpus artifact verina_basic_53,
  catalog title "CalSum": the executable natural-number recursion sums the
  numbers from one through N and satisfies the corresponding doubled-sum
  formula. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val CalSum_precond_def = new_definition (
  "CalSum_precond_def",
  ``CalSum_precond (N : num) <=> T``
);

val CalSum_loop_def = Define `
  (CalSum_loop 0 = 0) /\
  (CalSum_loop (SUC n) =
     SUC n + CalSum_loop n)
`;

val CalSum_def = new_definition (
  "CalSum_def",
  ``CalSum (N : num) =
      CalSum_loop N``
);

val CalSum_postcond_def = new_definition (
  "CalSum_postcond_def",
  ``CalSum_postcond (N : num) (result : num) <=>
      2 * result = N * (N + 1)``
);

val CalSum_spec_satisfied =
  ``!N : num.
      CalSum_precond N ==>
      CalSum_postcond N (CalSum N)``;
