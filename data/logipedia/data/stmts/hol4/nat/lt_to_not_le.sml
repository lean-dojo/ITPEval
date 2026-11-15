(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.lt_to_not_le (catalog title "nat.lt_to_not_le"): a strict inequality
  between natural numbers rules out the reverse non-strict inequality. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_lt_to_not_le =
  ``!(n : num) (m : num).
      n < m ==> ~(m <= n)``;
