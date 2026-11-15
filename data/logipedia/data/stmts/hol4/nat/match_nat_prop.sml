(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.match_nat_prop (catalog title "nat.match_nat_prop"): a predicate on the
  natural numbers that holds at zero and at every successor holds for every
  natural number, expressing exhaustive zero-or-successor case analysis. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_match_nat_prop =
  ``!P : num -> bool.
      P 0 ==>
      (!n : num. P (SUC n)) ==>
      !z : num. P z``;
