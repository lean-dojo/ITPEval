(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.plus_n_Sm (catalog title "nat.plus_n_Sm"): for all natural numbers
  n and m, the successor of n plus m equals n plus the successor of m.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_plus_n_Sm =
  ``!(n : num) (m : num).
      SUC (n + m) = n + SUC m``;
