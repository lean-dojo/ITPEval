(*
  Statement-only formalization of Hundred Theorems item 074, "The Principle
  of Mathematical Induction": a predicate on the natural numbers that holds
  at zero and is preserved by successor holds for every natural number. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val principle_of_mathematical_induction =
  ``!P : num -> bool.
      P 0 /\
      (!n : num. P n ==> P (SUC n))
      ==>
      !n : num. P n``;
