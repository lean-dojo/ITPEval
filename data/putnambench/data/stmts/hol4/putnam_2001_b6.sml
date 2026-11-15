(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2001_b6:
  every positive strictly increasing real sequence with a_n / n tending to
  zero has infinitely many strict midpoint-concavity indices. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_topologyTheory;

val putnam_2001_b6 =
  ``((!a : num -> real.
        (!n : num.
           1 <= n
           ==>
           0 < a n /\ a n < a (n + 1)) /\
        (((\n : num. a (n + 1) / &(n + 1)) --> 0) sequentially)
        ==>
        INFINITE
          {n : num |
             0 < n /\
             !i : num.
               1 <= i /\ i <= n - 1
               ==>
               a (n - i) + a (n + i) < 2 * a n})
      <=> T)``;
