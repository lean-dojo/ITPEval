(*
  Statement-only formalization of miniF2F test problem algebra_amgm_sumasqdivbgeqsuma: a cyclic
  inequality comparing a sum of squared positive reals divided by their successors with their
  sum. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val algebra_amgm_sumasqdivbgeqsuma =
  ``!a b c d : real.
      0 < a /\ 0 < b /\ 0 < c /\ 0 < d
      ==>
      a + b + c + d <=
        a pow 2 / b + b pow 2 / c + c pow 2 / d + d pow 2 / a``;
