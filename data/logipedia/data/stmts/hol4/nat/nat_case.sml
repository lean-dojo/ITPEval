(*
  Statement-only formalization of the Logipedia corpus artifact nat.nat_case
  (catalog title "nat.nat_case"): for any natural number and predicate, a
  zero case and a successor case selected by equality imply the predicate at
  that number. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_nat_case =
  ``!(n : num) (P : num -> bool).
      (n = 0 ==> P 0) ==>
      (!m : num. n = SUC m ==> P (SUC m)) ==>
      P n``;
