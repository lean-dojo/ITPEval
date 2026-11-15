(* Statement-only formalization of PutnamBench corpus artifact putnam_2003_b5:
   for a point inside the unit circle and three distinct pairwise equidistant
   points on its circumference, the distances to those points are the side
   lengths of a triangle whose area depends only on the point's distance from
   the center. This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_2003_b5_point : Type := (R * R)%type.

Definition putnam_2003_b5_origin : putnam_2003_b5_point := (0, 0).

Definition putnam_2003_b5_distance
    (p q : putnam_2003_b5_point) : R :=
  sqrt ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2).

Definition putnam_2003_b5_signed_twice_area
    (a b c : putnam_2003_b5_point) : R :=
  (fst b - fst a) * (snd c - snd a) -
  (snd b - snd a) * (fst c - fst a).

Definition putnam_2003_b5_triangle_area
    (a b c : putnam_2003_b5_point) : R :=
  Rabs (putnam_2003_b5_signed_twice_area a b c) / 2.

Theorem putnam_2003_b5
    (A B C : putnam_2003_b5_point)
    (hABC :
      putnam_2003_b5_distance putnam_2003_b5_origin A = 1 /\
      putnam_2003_b5_distance putnam_2003_b5_origin B = 1 /\
      putnam_2003_b5_distance putnam_2003_b5_origin C = 1 /\
      putnam_2003_b5_distance A B = putnam_2003_b5_distance A C /\
      putnam_2003_b5_distance A B = putnam_2003_b5_distance B C /\
      putnam_2003_b5_distance A B <> 0) :
  exists f : R -> R,
    forall P : putnam_2003_b5_point,
      putnam_2003_b5_distance putnam_2003_b5_origin P < 1 ->
      exists X Y Z : putnam_2003_b5_point,
        putnam_2003_b5_distance X Y = putnam_2003_b5_distance P A /\
        putnam_2003_b5_distance Y Z = putnam_2003_b5_distance P B /\
        putnam_2003_b5_distance X Z = putnam_2003_b5_distance P C /\
        putnam_2003_b5_triangle_area X Y Z =
          f (putnam_2003_b5_distance putnam_2003_b5_origin P).
Admitted.
