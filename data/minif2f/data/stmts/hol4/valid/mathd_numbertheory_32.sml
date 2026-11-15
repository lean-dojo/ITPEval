(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_32:
  the natural-number divisors of 36 sum to 91. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val mathd_numbertheory_32 =
  ``!S : num set.
      FINITE S /\
      (!n : num. n IN S <=> divides n 36)
      ==>
      SIGMA (\k : num. k) S = 91``;
