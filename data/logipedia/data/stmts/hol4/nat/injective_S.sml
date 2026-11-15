(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.injective_S (catalog title "nat.injective_S"): the successor function
  on the natural numbers is injective. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_injective_S =
  ``!(x : num) (y : num).
      SUC x = SUC y ==> x = y``;
