(*
  Statement-only formalization of miniF2F valid problem amc12b_2004_p3: natural-number
  exponents in 2^x * 3^y = 1296 determining x + y. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val _ = new_theory "hello";

val amc12b_2004_p3 =
  ``!x y : num.
      2 EXP x * 3 EXP y = 1296
      ==>
      x + y = 8``;

val _ = export_theory();
