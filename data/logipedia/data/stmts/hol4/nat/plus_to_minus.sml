(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.plus_to_minus (catalog title "nat.plus_to_minus"): if a natural number
  n equals m plus p, then subtracting m from n yields p. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_plus_to_minus =
  ``!(n : num) (m : num) (p : num).
      n = m + p ==> n - m = p``;
