(*
  Statement-only formalization of PutnamBench artifact putnam_1974_b3:
  a real number alpha satisfying cos (pi * alpha) = 1/3 is irrational.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory transcTheory;

val putnam_1974_b3 =
  ``!alpha : real.
      cos (pi * alpha) = 1 / 3
      ==>
      ~(?p q : int.
          q <> 0 /\
          alpha = real_of_int p / real_of_int q)``;
