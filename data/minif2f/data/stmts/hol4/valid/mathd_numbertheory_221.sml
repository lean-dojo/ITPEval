(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_221:
  exactly 11 positive natural numbers below 1000 have exactly three natural
  divisors. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val mathd_numbertheory_221 =
  ``CARD {x : num |
      0 < x /\
      x < 1000 /\
      CARD {d : num | divides d x} = 3} = 11``;
