(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1981_a3:
  nonexistence of a finite limit at positive infinity for an exponentially
  scaled iterated integral of a divided difference of the exponential
  function. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory transcTheory
     integrationTheory;

val putnam_1981_a3 =
  ``let f =
      \t : real.
        exp (-t) *
        integration$integral (interval [0, t])
          (\y : real.
             integration$integral (interval [0, t])
               (\x : real. (exp x - exp y) / (x - y)))
    in
      ~(?L : real. (f --> L) at_posinfinity)``;
