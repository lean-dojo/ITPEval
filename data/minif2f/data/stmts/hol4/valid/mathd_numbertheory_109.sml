(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_109: the sum of
  the first 100 odd natural numbers modulo 7. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val mathd_numbertheory_109 =
  ``!v : num -> num.
      (!n. v n = 2 * n - 1) ==>
      SIGMA v (IMAGE SUC (count 100)) MOD 7 = 4``;
