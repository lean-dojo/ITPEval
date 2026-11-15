(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q18206266, "Euclid–Euler theorem": every even perfect natural number is a
  power of two times a Mersenne prime. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val eq_two_pow_mul_prime_mersenne_of_even_perfect =
  ``!n : num.
      EVEN n /\
      0 < n /\
      SIGMA (\d : num. d) {d : num | divides d n} = 2 * n
      ==>
      ?k : num.
        prime (2 EXP (k + 1) - 1) /\
        n = 2 EXP k * (2 EXP (k + 1) - 1)``;
