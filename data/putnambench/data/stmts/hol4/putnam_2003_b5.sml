(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_b5:
  a triangle whose side lengths are the distances from an interior point to
  three equidistant points on the unit circle has area depending only on the
  interior point's distance from the center. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory transcTheory;

val putnam_2003_b5 =
  ``let origin = (0, 0) : real # real in
    let dist =
      \P Q : real # real.
        sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)
    in
    let triangle_area =
      \X Y Z : real # real.
        abs
          ((FST Y - FST X) * (SND Z - SND X) -
           (SND Y - SND X) * (FST Z - FST X)) / 2
    in
      !A B C : real # real.
        dist origin A = 1 /\
        dist origin B = 1 /\
        dist origin C = 1 /\
        dist A B = dist A C /\
        dist A B = dist B C /\
        dist A B <> 0
        ==>
        ?f : real -> real.
          !P : real # real.
            dist origin P < 1
            ==>
            ?X Y Z : real # real.
              dist X Y = dist P A /\
              dist Y Z = dist P B /\
              dist X Z = dist P C /\
              triangle_area X Y Z = f (dist origin P)``;
