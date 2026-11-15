(*
  Statement-only formalization of miniF2F test problem imo_1964_p2: a cyclic cubic inequality
  for positive real side lengths satisfying the strict triangle inequalities. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val imo_1964_p2 =
  ``!a b c : real.
      0 < a /\ 0 < b /\ 0 < c /\
      c < a + b /\
      b < a + c /\
      a < b + c
      ==>
      a pow 2 * (b + c - a) +
        b pow 2 * (c + a - b) +
        c pow 2 * (a + b - c) <=
      3 * a * b * c``;
