(*
  Statement-only formalization of PutnamBench artifact putnam_1974_a4:
  evaluation of a finite partial sum of binomial coefficients in closed form.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory pred_setTheory realTheory
     real_sigmaTheory;

val putnam_1974_a4 =
  ``!n : num.
      0 < n
      ==>
      1 / ((2 : real) pow (n - 1)) *
        SIGMA
          (\k : num.
             (&(n - 2 * k) : real) * &(binomial n k))
          (count (n DIV 2 + 1)) =
      (&n : real) / ((2 : real) pow (n - 1)) *
        &(binomial (n - 1) (n DIV 2))``;
