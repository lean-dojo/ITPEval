(*
  Statement-only formalization of PutnamBench artifact putnam_1970_b3:
  closedness of the y-axis projection of a closed subset of a bounded open
  vertical strip in the real plane. This file contains no proof.
*)

open HolKernel Parse boolLib;
open metricTheory topologyTheory realTheory real_topologyTheory;

val putnam_1970_b3 =
  ``!S : (real # real) set. !a b : real.
      a < b /\
      (!s : real # real.
         s IN S
         ==>
         a < FST s /\ FST s < b) /\
      closed_in (mtop mr2) S
      ==>
      closed {y : real | ?x : real. (x, y) IN S}``;
