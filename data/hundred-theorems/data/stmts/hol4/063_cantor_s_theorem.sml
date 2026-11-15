(*
  Statement-only formalization of "Cantor's Theorem" from Hundred Theorems item 063:
  no function from an arbitrary type to its predicates (its powerset representation)
  is surjective. This file contains no proof.
*)

open HolKernel Parse boolLib;

val cantor_s_theorem =
  ``!f : 'a -> 'a -> bool.
      ~(!s. ?x. f x = s)``;
