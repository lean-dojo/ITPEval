(*
  Statement-only formalization of PutnamBench artifact putnam_1968_a1:
  the identity expressing 22/7 minus pi as the definite integral on the unit
  interval of x^4(1-x)^4/(1+x^2). This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory integrationTheory;

val putnam_1968_a1 =
  ``22 / 7 - pi =
    integration$integral (interval [0, 1])
      (\x : real. x pow 4 * (1 - x) pow 4 / (1 + x pow 2))``;
