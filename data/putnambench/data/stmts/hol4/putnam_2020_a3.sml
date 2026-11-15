(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2020_a3:
  the squared terms of the real sine recurrence beginning at pi/2 have
  divergent partial sums. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory transcTheory;

val putnam_2020_a3 =
  ``let solution = F
    in
      !a : num -> real.
        a 0 = pi / 2 /\
        (!n : num. a (SUC n) = sin (a n))
        ==>
        ((?L : real.
            ((\N : num.
                SIGMA
                  (\n : num. (a n) pow 2)
                  (IMAGE SUC (count N))) --> L)
              sequentially)
         <=> solution)``;
