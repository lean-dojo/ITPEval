(*
  Statement-only formalization of miniF2F test problem amc12b_2002_p7: three positive
  consecutive natural numbers whose product is eight times their sum have squared sum 77.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val _ = new_theory "hello";

val amc12b_2002_p7 =
  ``!a b c : num.
      0 < a /\ 0 < b /\ 0 < c /\
      b = a + 1 /\
      c = b + 1 /\
      a * b * c = 8 * (a + b + c)
      ==>
      a ** 2 + (b ** 2 + c ** 2) = 77``;

val _ = export_theory();
