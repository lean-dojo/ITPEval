(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_plus_to_minus (catalog title "nat.le_plus_to_minus"): for natural
  numbers n, m, and p, n <= p + m implies n - m <= p, where subtraction is
  truncated natural-number subtraction. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_plus_to_minus =
  ``!(n : num) (m : num) (p : num).
      n <= p + m ==> n - m <= p``;
