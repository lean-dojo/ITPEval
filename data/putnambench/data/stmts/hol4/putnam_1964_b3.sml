(*
  Statement-only formalization of PutnamBench artifact putnam_1964_b3:
  a continuous real function that tends to zero along every positive
  arithmetic ray tends to zero at positive infinity. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_topologyTheory;

val putnam_1964_b3 =
  ``!f : real -> real.
      f continuous_on UNIV /\
      (!alpha : real.
         0 < alpha
         ==>
         ((\n : num. f (&n * alpha)) --> 0) sequentially)
      ==>
      !e : real.
        0 < e
        ==>
        ?M : real.
          !x : real.
            M <= x ==> abs (f x) < e``;
