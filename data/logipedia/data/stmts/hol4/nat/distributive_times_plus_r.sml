(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.distributive_times_plus_r (catalog title
  "nat.distributive_times_plus_r"): right multiplication by a natural
  number distributes over addition. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_distributive_times_plus_r =
  ``!(a : num) (b : num) (c : num).
      (b + c) * a = b * a + c * a``;
