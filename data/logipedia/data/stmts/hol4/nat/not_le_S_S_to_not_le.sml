(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.not_le_S_S_to_not_le (catalog title "nat.not_le_S_S_to_not_le"):
  if the successors of two natural numbers are not ordered by at most, then
  the original numbers are not ordered by at most. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_not_le_S_S_to_not_le =
  ``!(n : num) (m : num).
      ~(SUC n <= SUC m) ==> ~(n <= m)``;
