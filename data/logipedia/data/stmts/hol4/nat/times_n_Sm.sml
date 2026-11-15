(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.times_n_Sm (catalog title "nat.times_n_Sm"): for all natural numbers
  n and m, n plus n times m equals n times the successor of m. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_times_n_Sm =
  ``!(n : num) (m : num).
      n + n * m = n * SUC m``;
