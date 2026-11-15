(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2006_b2:
  every finite set of n real numbers, for positive n, has a nonempty subset
  whose sum is within 1 / (n + 1) of an integer. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory realTheory intrealTheory
  real_sigmaTheory;

val putnam_2006_b2 =
  ``!n : num. !X : real set.
      0 < n /\
      FINITE X /\
      CARD X = n
      ==>
      ?S : real set. ?m : int.
        S SUBSET X /\
        S <> {} /\
        abs (real_of_int m + SIGMA (\s : real. s) S) <=
          1 / (&n + 1)``;
