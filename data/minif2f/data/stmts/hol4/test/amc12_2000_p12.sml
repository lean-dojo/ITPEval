(*
  Statement-only formalization of miniF2F test problem amc12_2000_p12: a natural-number
  inequality under a fixed-sum constraint. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val amc12_2000_p12 =
  ``!a m c : num.
      (a + m + c = 12)
      ==>
      (a * m * c + a * m + m * c + a * c <= 112)``;
