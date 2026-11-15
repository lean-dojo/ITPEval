(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_343:
  the product of the first six positive odd natural numbers has remainder 5
  modulo 10. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val mathd_numbertheory_343 =
  ``PROD_IMAGE (\k : num. 2 * k + 1) (count 6) MOD 10 = 5``;
