(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_461:
  counting the natural numbers from 1 through 7 coprime to 8 and evaluating
  the corresponding power of 3 modulo 8. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory pred_setTheory;

val mathd_numbertheory_461 =
  ``!n : num.
      n = CARD {k : num | gcd k 8 = 1 /\ 1 <= k /\ k < 8}
      ==>
      (3 EXP n) MOD 8 = 1``;
