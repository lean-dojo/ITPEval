(*
  Statement-only formalization of Hundred Theorems artifact 066, "Sum of a Geometric Series":
  for real a and r with |r| < 1, the partial sums of a * r^n converge to a / (1 - r).
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory;

val sum_of_a_geometric_series =
  ``!a r : real.
      abs r < 1
      ==>
      ((\k : num.
          SIGMA
            (\n : num. a * r pow n)
            (count k)) --> (a / (1 - r) : real)) sequentially``;
