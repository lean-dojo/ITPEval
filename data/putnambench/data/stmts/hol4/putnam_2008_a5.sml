(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2008_a5:
  real polynomials whose values at 1 through n are the counterclockwise
  vertices of a regular n-gon, forcing one polynomial to have degree at least
  n - 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory transcTheory complexTheory polyTheory;

val putnam_2008_a5 =
  ``!n : num. !f g : real list.
      3 <= n /\
      (?center z : complex.
         z <> 0 /\
         !k : num.
           1 <= k /\ k <= n
           ==>
           complex_of_real (poly f (&k)) +
             i * complex_of_real (poly g (&k)) =
           center +
             z *
             complex_exp
               (i * complex_of_real (2 * pi * &k / &n)))
      ==>
      n - 1 <= degree f \/ n - 1 <= degree g``;
