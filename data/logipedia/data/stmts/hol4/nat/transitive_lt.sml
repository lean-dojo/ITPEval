(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.transitive_lt (catalog title "nat.transitive_lt"): strict order on
  the natural numbers is transitive. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_transitive_lt =
  ``!(a : num) (b : num) (c : num).
      a < b ==> b < c ==> a < c``;
