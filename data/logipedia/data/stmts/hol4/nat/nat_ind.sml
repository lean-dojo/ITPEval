(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.nat_ind (catalog title "nat.nat_ind"): a predicate on the natural
  numbers that holds at zero and is preserved by successor holds for every
  natural number. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_nat_ind =
  ``!(Q : num -> bool).
      Q 0 ==>
      (!x : num. Q x ==> Q (SUC x)) ==>
      !x : num. Q x``;
