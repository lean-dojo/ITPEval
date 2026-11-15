(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_35: the natural
  divisors of the square root of 196 have sum 24. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory logrootTheory pred_setTheory;

val _ = new_theory "hello";

val mathd_numbertheory_35 =
  ``!S : num set.
      FINITE S /\
      (!n : num. n IN S <=> divides n (SQRT 196))
      ==>
      SIGMA (\k : num. k) S = 24``;

val _ = export_theory();
