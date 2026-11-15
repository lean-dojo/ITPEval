(*
  Statement-only formalization of PutnamBench artifact putnam_1967_b5:
  for every positive integer n, the first n terms of the relevant negative
  binomial expansion sum to one half. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory pred_setTheory realTheory
     real_sigmaTheory;

val putnam_1967_b5 =
  ``!n : num.
      0 < n
      ==>
      (1 : real) / 2 =
      SIGMA
        (\i : num.
           (&(binomial (n + i - 1) i) : real) /
           ((2 : real) pow (n + i)))
        (count n)``;
