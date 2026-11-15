(*
  Statement-only formalization of miniF2F test problem amc12b_2020_p2: a real-number identity
  simplifying a product of quotients formed from differences of squares to 1. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val amc12b_2020_p2 =
  ``(((100 : real) pow 2 - 7 pow 2) /
      (70 pow 2 - 11 pow 2)) *
     ((70 - 11) * (70 + 11) /
      ((100 - 7) * (100 + 7))) =
    1``;
