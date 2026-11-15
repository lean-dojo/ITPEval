(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.lt_S_to_lt (catalog title "nat.lt_S_to_lt"): if the successor of a
  natural number is strictly less than another natural number, then the
  original number is strictly less than it. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_lt_S_to_lt =
  ``!(n : num) (m : num). SUC n < m ==> n < m``;
