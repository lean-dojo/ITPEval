(*
  Statement-only formalization of Hundred Theorems artifact 068, "Sum of an Arithmetic Series":
  for natural numbers a, d, and n, twice the sum of a + i * d over 0 <= i <= n
  equals (n + 1) * (2 * a + n * d). This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val sum_of_an_arithmetic_series =
  ``!a d n : num.
      2 * SIGMA (\i : num. a + i * d) (count (SUC n)) =
      SUC n * (2 * a + n * d)``;
