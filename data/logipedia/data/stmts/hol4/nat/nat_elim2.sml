(*
  Statement-only formalization of the Logipedia corpus artifact nat.nat_elim2
  (catalog title "nat.nat_elim2"): two-dimensional induction on natural
  numbers from the two zero-axis cases and a simultaneous successor step.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_nat_elim2 =
  ``!(R : num -> num -> bool).
      (!n : num. R 0 n) ==>
      (!n : num. R (SUC n) 0) ==>
      (!n : num. !m : num. R n m ==> R (SUC n) (SUC m)) ==>
      (!n : num. !m : num. R n m)``;
