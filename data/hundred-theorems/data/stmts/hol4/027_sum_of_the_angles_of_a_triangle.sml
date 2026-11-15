(*
  Statement-only formalization of "Sum of the Angles of a Triangle" from Hundred Theorems item
  027. This file contains no proof.
*)

(*
  Hundred Theorems item 027, "Sum of the Angles of a Triangle": the three Euclidean vertex
  angles of any triangle whose vertices are not all equal sum to pi. This statement-only
  formalization contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory transcTheory;

val sum_of_the_angles_of_a_triangle =
  ``let vertex_angle =
      \P Q R : real # real.
        if P = Q \/ R = Q then
          pi / 2
        else
          acs
            (((FST P - FST Q) * (FST R - FST Q) +
               (SND P - SND Q) * (SND R - SND Q)) /
             (sqrt ((FST P - FST Q) pow 2 +
                    (SND P - SND Q) pow 2) *
              sqrt ((FST R - FST Q) pow 2 +
                    (SND R - SND Q) pow 2)))
    in
      !A B C : real # real.
        ~(A = B /\ B = C /\ A = C) ==>
        vertex_angle B A C + vertex_angle A B C + vertex_angle B C A = pi``;
