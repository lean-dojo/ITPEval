(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.commutative_plus (catalog title "nat.commutative_plus"): addition on
  the natural numbers is commutative. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_commutative_plus =
  ``!(x : num) (y : num). x + y = y + x``;
