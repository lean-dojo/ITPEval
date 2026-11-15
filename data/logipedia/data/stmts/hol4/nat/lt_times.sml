(*
  Statement-only formalization of the Logipedia corpus artifact nat.lt_times
  (catalog title "nat.lt_times"): strict inequalities between natural numbers
  are preserved when the corresponding factors are multiplied. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_lt_times =
  ``!(n : num) (m : num) (p : num) (q : num).
      n < m ==>
      p < q ==>
      n * p < m * q``;
