(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.not_eq_to_le_to_lt (catalog title "nat.not_eq_to_le_to_lt"): for
  natural numbers, inequality together with non-strict order implies strict
  order. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_not_eq_to_le_to_lt =
  ``!(n : num) (m : num).
      ~(n = m) ==> n <= m ==> n < m``;
