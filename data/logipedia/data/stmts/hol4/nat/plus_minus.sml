(*
  Statement-only formalization of the Logipedia corpus artifact nat.plus_minus
  (catalog title "nat.plus_minus"): for natural numbers m <= n, adding p
  after subtracting m from n equals subtracting m after adding p to n.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_plus_minus =
  ``!(m : num) (n : num) (p : num).
      m <= n ==> (n - m) + p = (n + p) - m``;
