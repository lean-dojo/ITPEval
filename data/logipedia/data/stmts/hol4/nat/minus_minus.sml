(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.minus_minus (catalog title "nat.minus_minus"): if p is at most m and
  m is at most n, then p plus the difference n minus m equals n minus the
  difference m minus p. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_minus_minus =
  ``!(n : num) (m : num) (p : num).
      p <= m ==>
      m <= n ==>
      p + (n - m) = n - (m - p)``;
