(*
  Statement-only formalization of miniF2F valid problem amc12a_2021_p7: a universal lower
  bound for a sum of two squared real expressions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val amc12a_2021_p7 =
  ``!x y : real.
      1 <= (x * y - 1) pow 2 + (x + y) pow 2``;
