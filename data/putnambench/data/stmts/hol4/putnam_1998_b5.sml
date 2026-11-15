(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1998_b5:
  the thousandth digit after the decimal point of the square root of the
  1998-digit decimal repunit is 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory transcTheory;

val putnam_1998_b5 =
  ``let N = SIGMA (\i : num. 10 EXP i) (count 1998)
    in
      NUM_FLOOR ((10 : real) pow 1000 * sqrt (&N)) MOD 10 = 1``;
