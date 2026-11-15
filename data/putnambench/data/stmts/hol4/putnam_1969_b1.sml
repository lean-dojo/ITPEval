(*
  Statement-only formalization of PutnamBench artifact putnam_1969_b1:
  divisibility by 24 of the sum of all natural divisors of a positive
  integer whose successor is divisible by 24. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val putnam_1969_b1 =
  ``!n : num.
      0 < n /\ divides 24 (n + 1)
      ==>
      divides 24
        (SIGMA (\d : num. d) {d : num | divides d n})``;
