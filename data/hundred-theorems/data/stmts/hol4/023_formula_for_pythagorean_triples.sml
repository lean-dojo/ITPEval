(*
  Statement-only formalization of "Formula for Pythagorean Triples" from Hundred Theorems item
  023. It classifies integer solutions to x^2 + y^2 = z^2 by square-difference and double-product
  parameters, allowing the legs to be exchanged and either sign for z. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val formula_for_pythagorean_triples =
  ``!(x : int) (y : int) (z : int).
      x * x + y * y = z * z <=>
      ?k m n : int.
        ((x = k * (m * m - n * n) /\
          y = k * (2 * m * n)) \/
         (x = k * (2 * m * n) /\
          y = k * (m * m - n * n))) /\
        (z = k * (m * m + n * n) \/
         z = -k * (m * m + n * n))``;
