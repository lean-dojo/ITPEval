(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.times_Sn_m (catalog title "nat.times_Sn_m"): for all natural numbers
  n and m, m plus n times m equals (n + 1) times m. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_times_Sn_m =
  ``!(n : num) (m : num).
      m + n * m = SUC n * m``;
