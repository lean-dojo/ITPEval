(*
  Statement-only formalization of PutnamBench artifact putnam_1976_b5:
  the alternating binomial sum of the shifted powers (x - k)^n is the
  constant real polynomial n factorial. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory pred_setTheory realTheory
     real_sigmaTheory;

val putnam_1976_b5 =
  ``!n : num. !x : real.
      SIGMA
        (\k : num.
           (-1 : real) pow k *
           &(binomial n k) *
           (x - &k) pow n)
        (count (SUC n)) =
      &(FACT n)``;
