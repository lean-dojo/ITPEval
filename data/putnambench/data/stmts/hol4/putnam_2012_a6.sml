(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2012_a6:
  a continuous real function on the plane whose integral over every
  axis-aligned rectangle of area one is zero must vanish identically. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory metricTheory topologyTheory realTheory;
open real_topologyTheory integrationTheory;

val putnam_2012_a6 =
  ``!p : (real # real -> real) -> bool.
      (!f : real # real -> real.
         p f <=>
         continuous_map (mtop mr2, euclidean) f /\
         !x1 x2 y1 y2 : real.
           x1 < x2 /\
           y1 < y2 /\
           (x2 - x1) * (y2 - y1) = 1
           ==>
           integration$integral (interval [x1, x2])
             (\x : real.
                integration$integral (interval [y1, y2])
                  (\y : real. f (x, y))) =
           0)
      ==>
      ((!f : real # real -> real.
          !x y : real.
            p f ==> f (x, y) = 0)
       <=>
       T)``;
