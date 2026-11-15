(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q756946, "Lagrange's four-square theorem": every natural number is a sum
  of four squares of natural numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val lagrange_s_four_square_theorem =
  ``!n : num.
      ?a b c d : num.
        a EXP 2 + b EXP 2 + c EXP 2 + d EXP 2 = n``;
