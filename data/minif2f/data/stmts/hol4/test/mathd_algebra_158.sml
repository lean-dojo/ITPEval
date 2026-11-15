(*
  Statement-only formalization of miniF2F test problem mathd_algebra_158:
  determining an even natural number from the difference of two finite
  arithmetic sums. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val mathd_algebra_158 =
  ``!a : num.
      EVEN a /\
      int_of_num (SIGMA (\k. 2 * k + 1) (count 8)) -
        int_of_num (SIGMA (\k. a + 2 * k) (count 5)) = (4 : int)
      ==>
      a = 8``;
