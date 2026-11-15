(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_to_not_lt (catalog title "nat.le_to_not_lt"): for natural numbers
  n and m, n less than or equal to m implies that m is not less than n. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_to_not_lt =
  ``!(n : num) (m : num).
      n <= m ==> ~(m < n)``;
