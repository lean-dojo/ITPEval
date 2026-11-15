(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2004_a6:
  an inequality relating squared marginal integrals, the squared double
  integral, and the integral of the square of a continuous real function on
  the unit square. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory metricTheory topologyTheory realTheory;
open real_topologyTheory integrationTheory;

val putnam_2004_a6 =
  ``!f : real # real -> real.
      continuous_map
        (subtopology
           (mtop mr2)
           (interval [0, 1] CROSS interval [0, 1]),
         euclidean)
        f
      ==>
      integration$integral (interval [0, 1])
        (\y : real.
           (integration$integral (interval [0, 1])
              (\x : real. f (x, y))) pow 2) +
      integration$integral (interval [0, 1])
        (\x : real.
           (integration$integral (interval [0, 1])
              (\y : real. f (x, y))) pow 2) <=
      (integration$integral (interval [0, 1])
         (\y : real.
            integration$integral (interval [0, 1])
              (\x : real. f (x, y)))) pow 2 +
      integration$integral (interval [0, 1])
        (\y : real.
           integration$integral (interval [0, 1])
             (\x : real. (f (x, y)) pow 2))``;
