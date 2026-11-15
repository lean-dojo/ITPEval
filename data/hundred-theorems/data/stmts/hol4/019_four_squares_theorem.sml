(*
  Statement-only formalization of "Four Squares Theorem" from Hundred Theorems item 019. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val four_squares_theorem =
  ``!n : num.
      ?a b c d : num.
        n = a EXP 2 + b EXP 2 + c EXP 2 + d EXP 2``;
