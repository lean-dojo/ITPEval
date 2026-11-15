(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.minus_plus_m_m (catalog title "nat.minus_plus_m_m"): adding a natural
  number and then subtracting it by truncated natural subtraction recovers
  the original natural number. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_minus_plus_m_m =
  ``!(n : num) (m : num).
      n = (n + m) - m``;
