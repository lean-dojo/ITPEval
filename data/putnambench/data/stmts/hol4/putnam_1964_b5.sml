(*
  Statement-only formalization of PutnamBench artifact putnam_1964_b5:
  convergence of the reciprocal series of the successive least common
  multiples of a strictly increasing positive natural-number sequence.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory;

val putnam_1964_b5 =
  ``!a b : num -> num.
      (!m n : num. m < n ==> a m < a n) /\
      (!n : num. 0 < a n) /\
      b 0 = a 0 /\
      (!n : num. b (n + 1) = lcm (b n) (a (n + 1)))
      ==>
      ?L : real.
        ((\N : num.
            SIGMA
              (\n : num. (1 : real) / &(b n))
              (count N)) --> L) sequentially``;
