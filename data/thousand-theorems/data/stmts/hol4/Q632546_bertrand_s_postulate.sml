(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q632546, "Bertrand's postulate": every nonzero natural number has a prime
  strictly greater than it and no greater than twice it. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val bertrand =
  ``!n : num.
      n <> 0 ==>
      ?p : num. prime p /\ n < p /\ p <= 2 * n``;
