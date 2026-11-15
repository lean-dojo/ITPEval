(*
  Statement-only formalization of Logipedia corpus artifact nat.assoc_plus1
  (catalog title "nat.assoc_plus1"): an equality relating two associations
  and orders of addition for three natural numbers. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_assoc_plus1 =
  ``!a b c : num. c + (b + a) = (b + c) + a``;
