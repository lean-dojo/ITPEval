(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.associative_times (catalog title "nat.associative_times"):
  multiplication on the natural numbers is associative. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_associative_times =
  ``!(x : num) (y : num) (z : num).
      (x * y) * z = x * (y * z)``;
