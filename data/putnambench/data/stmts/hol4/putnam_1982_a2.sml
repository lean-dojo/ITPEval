(*
  Statement-only formalization of PutnamBench artifact putnam_1982_a2:
  convergence of the series defined from finite real-power sums evaluated at
  logarithms of 2 with varying bases. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory transcTheory;

val putnam_1982_a2 =
  ``let b =
      \n : num. \x : real.
        SIGMA
          (\k : num. (&k : real) powr x)
          (IMAGE SUC (count n))
    in
      let f =
        \n : num.
          b n (ln 2 / ln (&n : real)) /
          (((&n : real) * (ln (&n : real) / ln 2)) pow 2)
      in
        ((?L : real.
            ((\N : num.
                SIGMA
                  (\j : num. f j)
                  (IMAGE (\i : num. i + 2) (count (N - 1)))) --> L)
              sequentially)
         <=> T)``;
