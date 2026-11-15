(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.associative_plus (catalog title "nat.associative_plus"): addition on
  the natural numbers is associative. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_associative_plus =
  ``!(x : num) (y : num) (z : num).
      (x + y) + z = x + (y + z)``;
