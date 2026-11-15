(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_plus_minus_m_m (catalog title "nat.le_plus_minus_m_m"): every
  natural number is at most its truncated difference from another natural
  number plus that number. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_plus_minus_m_m =
  ``!(n : num) (m : num).
      n <= (n - m) + m``;
