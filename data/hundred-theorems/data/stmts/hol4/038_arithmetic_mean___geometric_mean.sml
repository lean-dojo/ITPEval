(*
  Statement-only formalization of "Arithmetic Mean / Geometric Mean" from Hundred Theorems item
  038. This file contains no proof.
*)

(*
  Hundred Theorems item 038, "Arithmetic Mean / Geometric Mean": for a nonempty finite sequence
  of nonnegative real numbers, the product is at most the nth power of its arithmetic mean.
  This is a statement-only formalization and contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val arithmetic_mean_geometric_mean =
  ``!n : num. !a : num -> real.
      1 <= n /\
      (!i. 1 <= i /\ i <= n ==> 0 <= a i)
      ==>
      REAL_PROD_IMAGE a (IMAGE SUC (count n)) <=
      (SIGMA a (IMAGE SUC (count n)) / &n) pow n``;
