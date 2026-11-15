(*
  Statement-only formalization of "The Fundamental Theorem of Algebra" from Hundred Theorems
  item 002. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory complexTheory listTheory;

val fundamental_theorem_of_algebra =
  ``!coeffs : complex list.
      1 < LENGTH coeffs /\
      LAST coeffs <> 0
      ==>
      ?z : complex.
        FOLDR (\c acc. c + z * acc) 0 coeffs = 0``;
