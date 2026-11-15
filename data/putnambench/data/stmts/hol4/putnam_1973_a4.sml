(*
  Statement-only formalization of PutnamBench artifact putnam_1973_a4:
  the function f(x) = 2^x - 1 - x^2 has exactly three zeros on the real
  line. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory;

val putnam_1973_a4 =
  ``{x : real | (2 : real) powr x - 1 - x pow 2 = 0} HAS_SIZE 3``;
