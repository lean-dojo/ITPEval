(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_a3:
  the real sequence beginning at 5/2 and satisfying a_k = a_(k-1)^2 - 2 has
  its prefix products of (1 - 1/a_k) converging to 3/7. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory;

val putnam_2014_a3 =
  ``!a : num -> real.
      a 0 = 5 / 2 /\
      (!k : num.
         1 <= k
         ==>
         a k = (a (k - 1)) pow 2 - 2)
      ==>
      ((\n : num.
          REAL_PROD_IMAGE
            (\k : num. 1 - 1 / a k)
            (count n)) -->
        (3 / 7))
      sequentially``;
