(*
  Statement-only formalization of the Logipedia corpus artifact nat.lt_to_le
  (catalog title "nat.lt_to_le"): strict order between natural numbers implies
  the corresponding non-strict order. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_lt_to_le =
  ``!(x : num) (y : num). x < y ==> x <= y``;
