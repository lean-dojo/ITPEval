(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_150:
  non-primality of 7 + 30 * n for a natural number n forces n to be at least 6.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val mathd_numbertheory_150 =
  ``!n : num.
      ~(prime (7 + 30 * n))
      ==>
      6 <= n``;
