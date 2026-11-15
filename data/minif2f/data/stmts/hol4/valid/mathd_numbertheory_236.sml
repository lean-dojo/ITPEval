(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_236:
  the natural-number remainder of 1999^2000 modulo 5 is 1. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_236 =
  ``((1999 : num) EXP 2000) MOD 5 = 1``;
