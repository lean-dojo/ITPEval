(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_a5:
  sums of 1994 terms at strictly increasing indices from a positive real
  sequence tending to zero leave a nonempty gap in every nonempty open
  interval. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory;

val putnam_1994_a5 =
  ``!r : num -> real. !S : real set.
      (!n : num. 0 < r n) /\
      ((r --> 0) sequentially) /\
      S =
        {x : real |
           ?i : num -> num.
             (!j k : num.
                j IN count 1994 /\ k IN count 1994 /\ j < k
                ==>
                i j < i k) /\
             x = SIGMA (\j : num. r (i j)) (count 1994)}
      ==>
      !a b : real.
        a < b
        ==>
        ?c d : real.
          a <= c /\
          c < d /\
          d <= b /\
          {x : real | c < x /\ x < d} INTER S = {}``;
