(*
  Statement-only formalization of PutnamBench artifact putnam_1971_a6:
  a real exponent whose positive integer powers are always integers is a
  nonnegative integer. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory transcTheory;

val putnam_1971_a6 =
  ``!c : real.
      (!n : int.
         n > 0
         ==>
         ?m : int.
           (real_of_int n) powr c = real_of_int m)
      ==>
      ?m : int.
        m >= 0 /\ c = real_of_int m``;
