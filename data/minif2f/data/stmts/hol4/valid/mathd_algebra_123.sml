(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_123: natural-number linear
  equations determining a subtraction result. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_algebra_123 =
  ``!a b : num.
      0 < a /\
      0 < b /\
      a + b = 20 /\
      a = 3 * b
      ==>
      a - b = 10``;
