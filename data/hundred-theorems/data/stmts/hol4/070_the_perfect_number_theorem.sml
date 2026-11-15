(*
  Statement-only formalization of "The Perfect Number Theorem" from Hundred
  Theorems artifact 070. It characterizes even positive natural numbers whose
  divisor sum is twice the number as exactly the numbers formed from a power
  of two and a Mersenne prime. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val perfect_number_theorem =
  ``!n : num.
      (EVEN n /\
       0 < n /\
       SIGMA (\d : num. d) {d : num | divides d n} = 2 * n)
      <=>
      ?k : num.
        prime (2 EXP (k + 1) - 1) /\
        n = 2 EXP k * (2 EXP (k + 1) - 1)``;
