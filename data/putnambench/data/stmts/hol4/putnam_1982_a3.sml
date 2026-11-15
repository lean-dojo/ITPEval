(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1982_a3:
  evaluation of the improper integral from zero to positive infinity of
  (arctan (pi * x) - arctan x) / x as (pi / 2) * ln pi.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory transcTheory
     integrationTheory;

val putnam_1982_a3 =
  ``((\t : real.
       integration$integral (interval [0, t])
         (\x : real. (atn (pi * x) - atn x) / x)) -->
     (pi / 2) * ln pi)
    at_posinfinity``;
