(*
  Statement-only formalization of PutnamBench artifact putnam_1977_a2:
  the classification of nonzero real quadruples satisfying a sum equation
  and its reciprocal equation. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val putnam_1977_a2 =
  ``!a b c d : real.
      a <> 0 /\ b <> 0 /\ c <> 0 /\ d <> 0
      ==>
      ((a + b + c = d /\
        1 / a + 1 / b + 1 / c = 1 / d)
       <=>
       (d = a /\ b = -c) \/
       (d = b /\ a = -c) \/
       (d = c /\ a = -b))``;
