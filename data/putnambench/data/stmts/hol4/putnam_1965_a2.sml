(*
  Statement-only formalization of PutnamBench artifact putnam_1965_a2:
  a finite binomial-coefficient sum identity for every positive integer.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory pred_setTheory realTheory
     real_sigmaTheory;

val putnam_1965_a2 =
  ``!n : num.
      0 < n
      ==>
      SIGMA
        (\r : num.
           (((&(n - 2 * r) : real) * &(binomial n r) / &n) pow 2))
        (count (SUC ((n - 1) DIV 2))) =
      (&(binomial (2 * n - 2) (n - 1)) : real) / &n``;
