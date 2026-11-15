(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1993_b4:
  positive continuous functions coupled by a positive continuous kernel on
  the unit square through reciprocal integral equations are equal on the
  unit interval. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory metricTheory topologyTheory realTheory;
open real_topologyTheory integrationTheory;

val putnam_1993_b4 =
  ``let unit_interval = interval [0, 1]
    in
    let unit_square =
      {p : real # real |
         FST p IN unit_interval /\ SND p IN unit_interval}
    in
      !K : real # real -> real.
      !f g : real -> real.
        (!x y : real.
           x IN unit_interval /\ y IN unit_interval
           ==>
           0 < K (x, y)) /\
        continuous_map
          (subtopology (mtop mr2) unit_square, euclidean) K /\
        (!x : real.
           x IN unit_interval
           ==>
           0 < f x /\ 0 < g x) /\
        f continuous_on unit_interval /\
        g continuous_on unit_interval /\
        (!x : real.
           x IN unit_interval
           ==>
           integration$integral unit_interval
             (\y : real. f y * K (x, y)) = g x /\
           integration$integral unit_interval
             (\y : real. g y * K (x, y)) = f x)
        ==>
        !x : real. x IN unit_interval ==> f x = g x``;
