(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_961:
  the natural-number remainder computation 2003 MOD 11 = 1. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_961 =
  ``((2003 : num) MOD 11 = 1)``;
