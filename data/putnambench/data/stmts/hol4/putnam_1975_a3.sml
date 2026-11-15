(*
  Statement-only formalization of PutnamBench artifact putnam_1975_a3:
  the explicit points where x^a + y^b + z^c attains its maximum and
  minimum on the nonnegative real surface x^b + y^b + z^b = 1 for
  0 < a < b < c. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory transcTheory;

val putnam_1975_a3 =
  ``!a b c : real.
      0 < a /\ a < b /\ b < c
      ==>
      let solution =
        ((\a b c : real.
            (((a / b) powr (1 / (b - a)),
              (1 - ((a / b) powr (1 / (b - a))) powr b)
                powr (1 / b)),
             0)),
         (\a b c : real.
            ((0,
              (1 - ((b / c) powr (1 / (c - b))) powr b)
                powr (1 / b)),
             (b / c) powr (1 / (c - b)))))
      in
      let feasible =
        \p : (real # real) # real.
          0 <= FST (FST p) /\
          0 <= SND (FST p) /\
          0 <= SND p /\
          FST (FST p) powr b +
            SND (FST p) powr b +
            SND p powr b = 1
      in
      let objective =
        \p : (real # real) # real.
          FST (FST p) powr a +
            SND (FST p) powr b +
            SND p powr c
      in
      let pmax = (FST solution) a b c in
      let pmin = (SND solution) a b c in
        (feasible pmax /\
         !x y z : real.
           feasible ((x, y), z) ==> objective ((x, y), z) <= objective pmax) /\
        (feasible pmin /\
         !x y z : real.
           feasible ((x, y), z) ==> objective pmin <= objective ((x, y), z))``;
