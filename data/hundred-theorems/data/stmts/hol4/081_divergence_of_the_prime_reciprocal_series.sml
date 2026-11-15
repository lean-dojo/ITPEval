(*
  Statement-only formalization of "Divergence of the Prime Reciprocal Series" from Hundred
  Theorems artifact 081. The real partial sums of reciprocals of natural primes grow without
  bound. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory realTheory real_sigmaTheory;

val divergence_of_the_prime_reciprocal_series =
  ``!B : real.
      ?N : num.
        !n : num.
          N <= n
          ==>
          B <=
            SIGMA
              (\p : num.
                 if prime p then (1 : real) / &p else 0)
              (count n)``;
