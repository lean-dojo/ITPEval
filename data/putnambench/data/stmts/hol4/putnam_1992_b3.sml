(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1992_b3:
  the planar Lebesgue measure of the initial points whose recursively defined
  real sequence converges is 4 + pi. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory real_topologyTheory;
open transcTheory extrealTheory measureTheory lebesgue_measureTheory
     martingaleTheory;

val putnam_1992_b3 =
  ``!a : (real # real) -> num -> real.
      (!p : real # real.
         a p 0 = FST p /\
         !n : num.
           a p (n + 1) =
             ((a p n) pow 2 + (SND p) pow 2) / 2)
      ==>
      measure
        (prod_measure_space lebesgue lebesgue)
        {p : real # real |
          ?L : real. (a p --> L) sequentially} =
      Normal (4 + pi)``;
