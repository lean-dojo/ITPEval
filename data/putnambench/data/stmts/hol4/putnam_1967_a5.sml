(*
  Statement-only formalization of PutnamBench artifact putnam_1967_a5:
  every convex region in the real Euclidean plane with area greater than
  pi / 4 contains two points exactly one unit apart. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory transcTheory;
open extrealTheory measureTheory lebesgue_measureTheory martingaleTheory;

val putnam_1967_a5 =
  ``!(R : (real # real) set).
      let convex_plane =
        \S : (real # real) set.
          !P Q : real # real. !u : real.
            P IN S /\ Q IN S /\ 0 <= u /\ u <= 1
            ==>
            ((1 - u) * FST P + u * FST Q,
             (1 - u) * SND P + u * SND Q) IN S
      in
      let dist =
        \P Q : real # real.
          sqrt
            ((FST P - FST Q) pow 2 +
             (SND P - SND Q) pow 2)
      in
        convex_plane R /\
        measure (prod_measure_space lebesgue lebesgue) R >
          Normal (pi / 4)
        ==>
        ?P Q : real # real.
          P IN R /\ Q IN R /\ dist P Q = 1``;
