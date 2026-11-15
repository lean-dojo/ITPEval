(*
  Statement-only formalization of miniF2F artifact mathd_algebra_289: prime coefficients and two
  natural roots of a quadratic determine a power sum. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory integerTheory;

val mathd_algebra_289 =
  ``!k t m n : num.
      prime m /\ prime n /\
      t < k /\
      int_of_num (k EXP 2) - int_of_num (m * k) + int_of_num n =
        (0 : int) /\
      int_of_num (t EXP 2) - int_of_num (m * t) + int_of_num n =
        (0 : int)
      ==>
      m EXP n + n EXP m + k EXP t + t EXP k = 20``;
