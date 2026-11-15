(*
  Statement-only formalization of the Logipedia corpus artifact nat.not_eq_S
  (catalog title "nat.not_eq_S"): unequal natural numbers have unequal
  successors. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_not_eq_S =
  ``!(n : num) (m : num).
      n <> m ==> SUC n <> SUC m``;
