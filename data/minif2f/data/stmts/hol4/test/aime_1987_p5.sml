(*
  Statement-only formalization of miniF2F test problem aime_1987_p5: an integer Diophantine
  equation determining the value of 3 times x squared times y squared. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val aime_1987_p5 =
  ``!x y : int.
      y ** 2 + 3 * (x ** 2 * y ** 2) = 30 * x ** 2 + 517
      ==>
      3 * (x ** 2 * y ** 2) = 588``;
