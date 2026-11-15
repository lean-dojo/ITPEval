(*
  Statement-only formalization of miniF2F valid problem amc12_2001_p2: natural-number digit
  bounds and two equations imply that the units digit b equals 9. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val amc12_2001_p2 =
  ``!a b n : num.
      (1 <= a /\ a <= 9) /\
      (0 <= b /\ b <= 9) /\
      (n = 10 * a + b) /\
      (n = a * b + a + b)
      ==>
      b = 9``;
