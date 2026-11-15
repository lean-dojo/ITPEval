(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.not_le_to_not_le_S_S (catalog title "nat.not_le_to_not_le_S_S"):
  for natural numbers n and m, if n is not less than or equal to m, then
  the successor of n is not less than or equal to the successor of m. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_not_le_to_not_le_S_S =
  ``!(n : num) (m : num).
      ~(n <= m) ==> ~(SUC n <= SUC m)``;
