(*
  Statement-only formalization of the Logipedia corpus artifact nat.minus_S_S
  (catalog title "nat.minus_S_S"): subtracting one successor natural number
  from another equals subtracting their predecessors. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_minus_S_S =
  ``!(n : num) (m : num).
      SUC n - SUC m = n - m``;
