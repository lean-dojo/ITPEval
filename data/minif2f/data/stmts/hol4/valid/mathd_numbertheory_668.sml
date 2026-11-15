(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_668:
  inverse residues of 5, 2, and 3 modulo 7 and their reduced difference.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_668 =
  ``!l r : num.
      l < 7 /\
      r < 7 /\
      (l * (2 + 3)) MOD 7 = 1 /\
      (?x y : num.
         x < 7 /\
         y < 7 /\
         (x * 2) MOD 7 = 1 /\
         (y * 3) MOD 7 = 1 /\
         r = (x + y) MOD 7)
      ==>
      l - r = 1``;
