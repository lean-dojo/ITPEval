(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_551:
  the natural-number remainder computation 1529 MOD 6 = 5. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_551 =
  ``1529 MOD 6 = 5``;
