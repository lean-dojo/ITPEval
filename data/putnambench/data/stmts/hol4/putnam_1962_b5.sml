(*
  Statement-only formalization of PutnamBench artifact putnam_1962_b5:
  strict lower and upper bounds for a finite sum of integer powers of
  normalized positive integers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory realTheory intrealTheory
     real_sigmaTheory transcTheory;

val putnam_1962_b5 =
  ``!n : int.
      n > 1
      ==>
      (3 * real_of_int n + 1) / (2 * real_of_int n + 2) <
        SIGMA
          (\i : num.
             ((&i : real) / real_of_int n) powr real_of_int n)
          (IMAGE SUC (count (Num n))) /\
      SIGMA
        (\i : num.
           ((&i : real) / real_of_int n) powr real_of_int n)
        (IMAGE SUC (count (Num n))) <
        2``;
