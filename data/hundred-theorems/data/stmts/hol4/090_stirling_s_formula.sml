(*
  Statement-only formalization of Hundred Theorems artifact
  hundred-theorems__hol4__090, cataloged as "Stirling's Formula": the
  factorial normalized by sqrt(2n) times (n/e)^n converges to sqrt(pi).
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory transcTheory real_topologyTheory;

val stirling_s_formula =
  ``((\n : num.
       &(FACT n) /
       (sqrt (2 * &n) * ((&n / exp 1) pow n))) -->
      sqrt pi) sequentially``;
