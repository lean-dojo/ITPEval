(*
  Statement-only formalization of the Logipedia corpus artifact nat.le_ind
  (catalog title "nat.le_ind"): lower-bounded induction on natural numbers
  with a base case and successor step. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_ind =
  ``!n : num.
      !(Q : num -> bool).
        Q n ==>
        (!m : num. n <= m ==> Q m ==> Q (SUC m)) ==>
        (!m : num. n <= m ==> Q m)``;
