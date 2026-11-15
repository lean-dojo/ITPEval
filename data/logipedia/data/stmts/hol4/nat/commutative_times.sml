(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.commutative_times (catalog title "nat.commutative_times"):
  multiplication on the natural numbers is commutative. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_commutative_times =
  ``!(x : num) (y : num). x * y = y * x``;
