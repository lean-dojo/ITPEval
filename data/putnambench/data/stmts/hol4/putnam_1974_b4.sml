(*
  Statement-only formalization of PutnamBench artifact putnam_1974_b4:
  every separately continuous real function on the plane is the pointwise
  limit of a sequence of jointly continuous real functions. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory metricTheory real_topologyTheory;

val putnam_1974_b4 =
  ``!f : real # real -> real.
      (!y : real. (\x : real. f (x, y)) continuous_on UNIV) /\
      (!x : real. (\y : real. f (x, y)) continuous_on UNIV)
      ==>
      ?g : num -> real # real -> real.
        (!n : num. continuous_map (mtop mr2, euclidean) (g n)) /\
        (!x y : real.
           ((\n : num. g n (x, y)) --> f (x, y)) sequentially)``;
