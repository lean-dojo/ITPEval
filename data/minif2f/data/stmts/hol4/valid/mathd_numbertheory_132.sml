(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_132:
  the natural-number remainder computation 2004 MOD 12 = 0. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_132 =
  ``2004 MOD 12 = 0``;
