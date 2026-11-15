(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.injective_plus_r (catalog title "nat.injective_plus_r"): for each
  natural number, adding it on the left is injective in the right argument.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_injective_plus_r =
  ``!(n : num) (x : num) (y : num).
      n + x = n + y ==> x = y``;
