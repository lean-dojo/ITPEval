(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.transitive_le (catalog title "nat.transitive_le"): less-than-or-equal
  on the natural numbers is transitive. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_transitive_le =
  ``!(a : num) (b : num) (c : num).
      a <= b ==> b <= c ==> a <= c``;
