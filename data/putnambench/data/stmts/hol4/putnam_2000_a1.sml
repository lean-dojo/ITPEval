(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2000_a1:
  for positive A, the possible sums of squares of positive real sequences
  with sum A form the open interval from 0 to A squared. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory seqTheory;

val putnam_2000_a1 =
  ``!A : real.
      0 < A
      ==>
      {s : real |
         ?x : num -> real.
           (!j : num. 0 < x j) /\
           x sums A /\
           (\j : num. (x j) pow 2) sums s} =
      {s : real | 0 < s /\ s < A pow 2}``;
