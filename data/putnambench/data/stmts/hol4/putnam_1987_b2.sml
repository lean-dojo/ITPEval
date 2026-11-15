(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1987_b2:
  the finite reciprocal-binomial sum identity for natural numbers r, s, and t
  satisfying r + s <= t. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory pred_setTheory realTheory
     real_sigmaTheory;

val putnam_1987_b2 =
  ``!r s t : num.
      r + s <= t
      ==>
      SIGMA
        (\i : num.
           (&(binomial s i) : real) /
           &(binomial t (r + i)))
        (count (s + 1)) =
      (&t + 1) /
        ((&t + 1 - &s) * &(binomial (t - s) r))``;
