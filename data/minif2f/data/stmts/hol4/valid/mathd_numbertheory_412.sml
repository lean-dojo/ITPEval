(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_412:
  specified residues of two natural numbers modulo 19 determine the residue of
  a product of powers modulo 19. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_412 =
  ``!x y : num.
      x MOD 19 = 4 /\
      y MOD 19 = 7
      ==>
      ((x + 1) EXP 2 * (y + 5) EXP 3) MOD 19 = 13``;
