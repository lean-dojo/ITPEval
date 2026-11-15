(*
  Statement-only formalization of miniF2F valid problem amc12a_2009_p25: a natural-indexed real
  sequence with specified initial values and a rational recurrence has zero absolute value at
  index 2009. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val _ = new_theory "hello";

val amc12a_2009_p25 =
  ``!a : num -> real.
      a 1 = 1 /\
      a 2 = 1 / sqrt 3 /\
      (!n : num.
         1 <= n ==>
         a (n + 2) =
           (a n + a (n + 1)) / (1 - a n * a (n + 1)))
      ==>
      abs (a 2009) = 0``;

val _ = export_theory();
