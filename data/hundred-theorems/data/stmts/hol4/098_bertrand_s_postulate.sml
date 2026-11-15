(*
  Statement-only formalization of "Bertrand's Postulate" from Hundred
  Theorems artifact hundred-theorems__hol4__098: every positive natural
  number has a prime strictly greater than it and no greater than twice it.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val bertrand_s_postulate =
  ``!n : num.
      n <> 0 ==>
      ?p : num. prime p /\ n < p /\ p <= 2 * n``;
