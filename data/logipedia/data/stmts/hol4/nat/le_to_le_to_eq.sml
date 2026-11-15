(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_to_le_to_eq (catalog title "nat.le_to_le_to_eq"): two natural
  numbers that are each less than or equal to the other are equal. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_to_le_to_eq =
  ``!(n : num) (m : num).
      n <= m ==> m <= n ==> n = m``;
