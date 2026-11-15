(*
  Statement-only formalization of "Leibniz's Series for Pi" from Hundred Theorems item 026. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory transcTheory;
open real_topologyTheory;

val leibniz_series_for_pi =
  ``((\k : num.
       SIGMA
         (\i : num. (~1 : real) pow i / &(2 * i + 1))
         (count k)) --> (pi / 4 : real)) sequentially``;
