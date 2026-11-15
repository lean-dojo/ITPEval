(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2008_b3:
  the greatest radius of a circle contained in the four-dimensional unit
  hypercube is sqrt 2 / 2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory transcTheory;

val putnam_2008_b3 =
  ``let zero4 = ((0, 0), (0, 0)) : (real # real) # (real # real)
    in
    let add4 =
      \P Q : (real # real) # (real # real).
        ((FST (FST P) + FST (FST Q),
          SND (FST P) + SND (FST Q)),
         (FST (SND P) + FST (SND Q),
          SND (SND P) + SND (SND Q)))
    in
    let smul4 =
      \c : real.
      \P : (real # real) # (real # real).
        ((c * FST (FST P), c * SND (FST P)),
         (c * FST (SND P), c * SND (SND P)))
    in
    let norm4 =
      \P : (real # real) # (real # real).
        sqrt
          (FST (FST P) pow 2 +
           SND (FST P) pow 2 +
           FST (SND P) pow 2 +
           SND (SND P) pow 2)
    in
    let in_hypercube =
      \P : (real # real) # (real # real).
        abs (FST (FST P)) <= 1 / 2 /\
        abs (SND (FST P)) <= 1 / 2 /\
        abs (FST (SND P)) <= 1 / 2 /\
        abs (SND (SND P)) <= 1 / 2
    in
    let independent =
      \P Q : (real # real) # (real # real).
        !a b : real.
          add4 (smul4 a P) (smul4 b Q) = zero4
          ==>
          a = 0 /\ b = 0
    in
    let contains_circle =
      \r : real.
        ?C P Q : (real # real) # (real # real).
          independent P Q /\
          !s t : real.
            norm4 (add4 (smul4 s P) (smul4 t Q)) = r
            ==>
            in_hypercube
              (add4 C (add4 (smul4 s P) (smul4 t Q)))
    in
    let solution = sqrt 2 / 2
    in
      contains_circle solution /\
      !r : real. solution < r ==> ~contains_circle r``;
