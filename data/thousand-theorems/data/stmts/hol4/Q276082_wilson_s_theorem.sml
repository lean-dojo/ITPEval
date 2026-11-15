(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q276082, "Wilson's theorem": for every prime natural number p, (p - 1)! is
  congruent to -1 modulo p. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val wilsons_lemma =
  ``!p : num.
      prime p ==>
      (FACT (p - 1)) MOD p = (p - 1) MOD p``;
