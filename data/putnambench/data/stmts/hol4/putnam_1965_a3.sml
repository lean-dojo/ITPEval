(*
  Statement-only formalization of PutnamBench artifact putnam_1965_a3:
  for any real sequence, convergence of its complex exponential Cesaro
  averages is equivalent to convergence of the averages indexed by squares.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory transcTheory;
open complexTheory real_topologyTheory;

val putnam_1965_a3 =
  ``!a : num -> real. !alpha : complex.
      let real_average =
        \N : num.
          SIGMA
            (\k : num. cos (a k))
            (IMAGE SUC (count N)) / &N
      in
      let imag_average =
        \N : num.
          SIGMA
            (\k : num. sin (a k))
            (IMAGE SUC (count N)) / &N
      in
        ((real_average --> RE alpha) sequentially /\
         (imag_average --> IM alpha) sequentially)
        <=>
        (((\n : num. real_average (n EXP 2)) --> RE alpha) sequentially /\
         ((\n : num. imag_average (n EXP 2)) --> IM alpha) sequentially)``;
