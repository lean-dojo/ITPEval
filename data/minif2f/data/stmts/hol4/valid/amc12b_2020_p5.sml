(*
  Statement-only formalization of miniF2F valid problem amc12b_2020_p5. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val amc12b_2020_p5 =
  ``!a b : num.
      ((5 : real) / 8 * &b = 2 / 3 * &a + 7) /\
      (&b - 5 / 8 * &b = &a - 2 / 3 * &a + 7)
      ==>
      a = 42``;
