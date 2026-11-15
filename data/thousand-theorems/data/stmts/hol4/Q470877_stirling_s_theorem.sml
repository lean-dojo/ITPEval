(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q470877, "Stirling's theorem": the factorial normalized by sqrt(2n) times
  (n/e)^n converges to sqrt(pi). This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory transcTheory real_topologyTheory;

val tendsto_stirlingSeq_sqrt_pi =
  ``((\n : num.
       &(FACT n) /
       (sqrt (2 * &n) * ((&n / exp 1) pow n))) -->
      sqrt pi) sequentially``;
