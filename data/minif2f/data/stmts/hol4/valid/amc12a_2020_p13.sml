(*
  Statement-only formalization of miniF2F valid problem amc12a_2020_p13: a nested positive-real
  reciprocal-power identity implying that the middle denominator b equals 3. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory transcTheory;

val _ = new_theory "hello";

val amc12a_2020_p13 =
  ``!a b c : num. !n : real.
      0 < n /\
      ~(n = 1) /\
      1 < a /\ 1 < b /\ 1 < c /\
      (n * ((n * (n powr (1 / &c))) powr (1 / &b))) powr (1 / &a) =
        (n pow 25) powr (1 / 36)
      ==>
      b = 3``;

val _ = export_theory();
