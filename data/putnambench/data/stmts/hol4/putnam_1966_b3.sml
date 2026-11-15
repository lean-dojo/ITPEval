(*
  Statement-only formalization of PutnamBench artifact putnam_1966_b3:
  convergence of a reciprocal series for a positive real sequence implies
  convergence of a series formed from squared indices and partial sums.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory;

val putnam_1966_b3 =
  ``!p : num -> real.
      (!n : num. 0 < p n) /\
      (?r : real.
         ((\m : num.
             SIGMA
               (\n : num. (1 : real) / p n)
               (IMAGE SUC (count m))) --> r) sequentially)
      ==>
      ?r : real.
        ((\m : num.
            SIGMA
              (\n : num.
                 p n * ((&n : real) pow 2) /
                 ((SIGMA
                     (\i : num. p i)
                     (IMAGE SUC (count n))) pow 2))
              (IMAGE SUC (count m))) --> r) sequentially``;
