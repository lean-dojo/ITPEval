(*
  Statement-only formalization of miniF2F test problem imo_1974_p3: non-divisibility
  by 5 of a finite sum of weighted binomial coefficients. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory dividesTheory pred_setTheory;

val imo_1974_p3 =
  ``!n : num.
      ~(5 divides
        (SIGMA
          (\k. binomial (2 * n + 1) (2 * k + 1) * 2 ** (3 * k))
          (count (n + 1))))``;
