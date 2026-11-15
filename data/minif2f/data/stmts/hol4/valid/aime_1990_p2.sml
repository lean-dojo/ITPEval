(*
  Statement-only formalization of miniF2F valid problem aime_1990_p2: a real-exponentiation
  identity for conjugate expressions involving sqrt 43. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val aime_1990_p2 =
  ``((52 : real) + 6 * sqrt 43) powr (3 / 2 : real) -
      ((52 : real) - 6 * sqrt 43) powr (3 / 2 : real) = 828``;
