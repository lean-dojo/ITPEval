(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_239:
  the sum of the natural numbers from 1 through 12 has remainder 2 modulo 4.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val mathd_numbertheory_239 =
  ``SIGMA (\k : num. k) (IMAGE SUC (count 12)) MOD 4 = 2``;
