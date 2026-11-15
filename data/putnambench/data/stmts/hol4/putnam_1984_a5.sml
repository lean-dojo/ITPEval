(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1984_a5:
  evaluation of a monomial triple integral over the nonnegative unit simplex
  as a quotient of factorials. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory integrationTheory;

val putnam_1984_a5 =
  ``0 < (1 : num) /\ 0 < (9 : num) /\ 0 < (8 : num) /\
    0 < (4 : num) /\ 0 < (25 : num) /\
    integration$integral (interval [0, 1])
      (\z : real.
         integration$integral (interval [0, 1 - z])
           (\y : real.
              integration$integral (interval [0, 1 - y - z])
                (\x : real.
                   x pow 1 * y pow 9 * z pow 8 *
                   (1 - x - y - z) pow 4))) =
    (&(FACT 1) * &(FACT 9) * &(FACT 8) * &(FACT 4)) / &(FACT 25)``;
