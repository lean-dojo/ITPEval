(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.minus_to_plus (catalog title "nat.minus_to_plus"): if subtracting a
  smaller natural number m from n yields p, then n equals m plus p. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_minus_to_plus =
  ``!(n : num) (m : num) (p : num).
      m <= n ==> n - m = p ==> n = m + p``;
