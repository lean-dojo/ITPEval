(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.plus_minus_m_m (catalog title "nat.plus_minus_m_m"): for natural
  numbers m <= n, adding m to the truncated difference n - m recovers n.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_plus_minus_m_m =
  ``!(n : num) (m : num).
      m <= n ==> n = (n - m) + m``;
