(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q188295, "Fermat's little theorem": for a prime modulus p, every nonzero
  residue class modulo p raised to the power p - 1 is congruent to one.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val fermats_little_theorem =
  ``!p a : num.
      prime p /\
      a MOD p <> 0
      ==>
      (a EXP (p - 1)) MOD p = (1 MOD p)``;
