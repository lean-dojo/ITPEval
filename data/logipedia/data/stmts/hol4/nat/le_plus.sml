(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_plus (catalog title "nat.le_plus"): addition is monotone in both
  arguments for the natural-number order. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_plus =
  ``!(n1 : num) (n2 : num) (m1 : num) (m2 : num).
      n1 <= n2 ==> m1 <= m2 ==> n1 + m1 <= n2 + m2``;
