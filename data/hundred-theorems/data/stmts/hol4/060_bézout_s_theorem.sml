(*
  Statement-only formalization of "Bézout's Theorem" from Hundred Theorems artifact 060.
  For every pair of integers, integer coefficients form a linear combination equal to
  their nonnegative greatest common divisor. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory integerTheory;

val bezouts_theorem =
  ``!(x : int) (y : int).
      ?u v : int.
        u * x + v * y =
        &(gcd (Num (ABS x)) (Num (ABS y)))``;
