(*
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2011_a3: the positive limiting value of a ratio of sine- and
  cosine-weighted real-power integrals on (0, pi/2), after normalization by
  a real power of the parameter. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory netsTheory real_topologyTheory;
open extrealTheory measureTheory borelTheory lebesgueTheory;

val putnam_2011_a3 =
  ``let c = (-1 : real) in
    let L = 2 / pi in
    let domain = {x : real | 0 < x /\ x < pi / 2} in
      L > 0 /\
      ((\r : real.
          (r powr c *
             real
               (integral lborel
                 (\x.
                    Normal (x powr r * sin x) *
                    indicator_fn domain x))) /
          real
            (integral lborel
              (\x.
                 Normal (x powr r * cos x) *
                 indicator_fn domain x))) -->
       L) at_posinfinity``;
