(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1983_a6:
  evaluation of the positive-infinity limit of an exponentially normalized
  iterated integral over a right triangle. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory transcTheory
     integrationTheory;

val putnam_1983_a6 =
  ``let F =
      \a : real.
        (a pow 4 / exp (a pow 3)) *
        integration$integral (interval [0, a])
          (\x : real.
             integration$integral (interval [0, a - x])
               (\y : real. exp (x pow 3 + y pow 3)))
    in
      (F --> (2 / 9 : real)) at_posinfinity``;
