(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1989_a2:
  evaluation of a double integral of the exponential of a maximum over a
  positive rectangular region. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory integrationTheory;

val putnam_1989_a2 =
  ``!a b : real.
      0 < a /\ 0 < b
      ==>
      integration$integral (interval [0, a])
        (\x : real.
           integration$integral (interval [0, b])
             (\y : real.
                exp
                  (max (b pow 2 * x pow 2)
                       (a pow 2 * y pow 2)))) =
      (exp (a pow 2 * b pow 2) - 1) / (a * b)``;
