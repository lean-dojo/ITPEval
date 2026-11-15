(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1982_b3:
  the limit of the probability that the sum of two independent uniform
  choices from {1, ..., n} is a perfect square. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory;
open real_topologyTheory transcTheory;

val putnam_1982_b3 =
  ``let p =
      \n : num.
        &(CARD
            {cd : num # num |
               let c = FST cd in
               let d = SND cd in
                 1 <= c /\ c <= n /\
                 1 <= d /\ d <= n /\
                 ?m : num. m ** 2 = c + d}) /
        (&n : real) pow 2
    in
      (((\n : num. p n * sqrt (&n)) : num -> real) -->
       ((4 / 3) * (sqrt 2 - 1) : real)) sequentially``;
