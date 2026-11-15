(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_353:
  if a natural number is the sum of the natural numbers from 2010 through
  4018, then it is divisible by 2009. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val mathd_numbertheory_353 =
  ``!s : num.
      s = SIGMA (\k : num. k)
            (IMAGE (\i : num. 2010 + i) (count 2009))
      ==>
      s MOD 2009 = 0``;
