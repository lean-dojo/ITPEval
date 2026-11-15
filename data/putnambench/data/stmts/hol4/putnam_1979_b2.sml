(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1979_b2:
  the punctured limit at zero of a real-power integral over the unit interval,
  with its explicit value in terms of two positive endpoints. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory transcTheory;
open extrealTheory measureTheory borelTheory lebesgueTheory
     lebesgue_measureTheory;

val putnam_1979_b2 =
  ``!a b : real.
      0 < a /\ a < b
      ==>
      let unit_interval =
        restrict_space lebesgue (interval [0, 1])
      in
        ((\t : real.
            (real
               (lebesgue$integral unit_interval
                  (\x : real.
                     Normal ((b * x + a * (1 - x)) powr t))))
              powr (1 / t)) -->
         exp (-1) *
           ((b powr b / a powr a) powr (1 / (b - a))))
          (at 0)``;
