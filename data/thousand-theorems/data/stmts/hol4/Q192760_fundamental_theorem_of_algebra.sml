(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q192760 (thousand-theorems__hol4__Q192760), "Fundamental theorem of
  algebra": every nonconstant polynomial with complex coefficients has a
  complex root, equivalently the complex numbers are algebraically closed.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory complexTheory listTheory;

val complex_is_alg_closed =
  ``!coeffs : complex list.
      1 < LENGTH coeffs /\
      LAST coeffs <> 0
      ==>
      ?z : complex.
        FOLDR (\c acc. c + z * acc) 0 coeffs = 0``;
