(*
  Statement-only formalization of PutnamBench artifact putnam_1970_b2:
  the two-point Gaussian quadrature identity for the average of a real
  polynomial of degree at most three on a symmetric interval. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory integrationTheory polyTheory;

val putnam_1970_b2 =
  ``!T : real. !H : real list.
      0 < T /\ degree H <= 3
      ==>
      (poly H (~T / sqrt 3) + poly H (T / sqrt 3)) / 2 =
      1 / (2 * T) *
        integration$integral (interval [~T, T]) (poly H)``;
