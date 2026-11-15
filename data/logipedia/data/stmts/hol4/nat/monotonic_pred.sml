(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.monotonic_pred (catalog title "nat.monotonic_pred"): the predecessor
  function is monotone with respect to the natural-number order. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_monotonic_pred =
  ``!(n : num) (m : num).
      n <= m ==> PRE n <= PRE m``;
