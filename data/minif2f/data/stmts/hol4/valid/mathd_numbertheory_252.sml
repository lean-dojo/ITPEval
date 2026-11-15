(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_252:
  the natural-number factorial remainder computation 7! MOD 23 = 3. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_252 =
  ``(FACT 7) MOD 23 = 3``;
