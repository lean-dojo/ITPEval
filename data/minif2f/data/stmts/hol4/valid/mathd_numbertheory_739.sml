(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_739:
  the natural-number factorial remainder computation 9! MOD 10 = 0. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_739 =
  ``(FACT 9) MOD 10 = 0``;
