(*
  Statement-only formalization of PutnamBench artifact putnam_1975_b4:
  the nonexistence of a topologically closed subset of the real unit circle
  containing exactly one point from each antipodal pair. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory metricTheory topologyTheory realTheory;
open real_topologyTheory;

val putnam_1975_b4 =
  ``let P =
      \p : real # real.
        FST p pow 2 + SND p pow 2 = 1
    in
    let putnam_1975_b4_solution = F
    in
      ((?B : (real # real) set.
          B SUBSET {p : real # real | P p} /\
          closed_in (mtop mr2) B /\
          !x y : real.
            P (x, y)
            ==>
            ~(((x, y) IN B) <=> ((-x, -y) IN B)))
       <=>
       putnam_1975_b4_solution)``;
