(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_37:
  the least common multiple of 9999 and 100001 is 90900909. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory;

val mathd_numbertheory_37 =
  ``lcm 9999 100001 = 90900909``;
