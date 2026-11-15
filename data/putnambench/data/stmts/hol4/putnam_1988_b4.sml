(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_b4:
  a convergent series of positive real terms remains convergent after each
  term is raised to the power n/(n+1). This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory transcTheory;

val putnam_1988_b4 =
  ``let is_pos_conv =
      \a : num -> real.
        (!n : num. 1 <= n ==> 0 < a n) /\
        (?s : real.
           ((\N : num.
               SIGMA a (IMAGE SUC (count N))) --> s) sequentially)
    in
      !a : num -> real.
        is_pos_conv a
        ==>
        is_pos_conv
          (\n : num. a n powr (&n / (&n + 1)))``;
