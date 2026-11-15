(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_b6:
  a continuous real function satisfies the stated lower bound comparing the
  double integral of |f(x) + f(y)| on the unit square with the integral of
  |f(x)| on the unit interval. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory integrationTheory;

val putnam_2003_b6 =
  ``!f : real -> real.
      f continuous_on UNIV
      ==>
      integration$integral (interval [0, 1])
        (\x : real.
           integration$integral (interval [0, 1])
             (\y : real. abs (f x + f y))) >=
      integration$integral (interval [0, 1])
        (\x : real. abs (f x))``;
