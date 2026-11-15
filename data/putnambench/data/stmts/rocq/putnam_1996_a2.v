(* Statement-only formalization of PutnamBench corpus artifact putnam_1996_a2:
   the locus of midpoints of pairs of points on two circles of radii one and
   three is a closed annulus about the midpoint of their centers. This file
   contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_1996_a2_point : Type :=
  (R * R)%type.

Definition putnam_1996_a2_point_set : Type :=
  putnam_1996_a2_point -> Prop.

Definition putnam_1996_a2_distance
    (p q : putnam_1996_a2_point) : R :=
  sqrt ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2).

Definition putnam_1996_a2_midpoint
    (p q : putnam_1996_a2_point) : putnam_1996_a2_point :=
  ((fst p + fst q) / 2, (snd p + snd q) / 2).

Definition putnam_1996_a2_circle
    (center : putnam_1996_a2_point) (radius : R) :
    putnam_1996_a2_point_set :=
  fun p : putnam_1996_a2_point =>
    putnam_1996_a2_distance p center = radius.

Definition putnam_1996_a2_locus
    (C1 C2 : putnam_1996_a2_point_set) :
    putnam_1996_a2_point_set :=
  fun M : putnam_1996_a2_point =>
    exists X Y : putnam_1996_a2_point,
      C1 X /\
      C2 Y /\
      M = putnam_1996_a2_midpoint X Y.

Definition putnam_1996_a2_solution
    (O1 O2 : putnam_1996_a2_point) :
    putnam_1996_a2_point_set :=
  fun p : putnam_1996_a2_point =>
    1 <=
      putnam_1996_a2_distance p
        (putnam_1996_a2_midpoint O1 O2) /\
    putnam_1996_a2_distance p
      (putnam_1996_a2_midpoint O1 O2) <= 2.

Theorem putnam_1996_a2
    (O1 O2 : putnam_1996_a2_point)
    (C1 C2 : putnam_1996_a2_point_set)
    (hC1 : C1 = putnam_1996_a2_circle O1 1)
    (hC2 : C2 = putnam_1996_a2_circle O2 3)
    (hO1O2 : putnam_1996_a2_distance O1 O2 = 10) :
  forall M : putnam_1996_a2_point,
    putnam_1996_a2_locus C1 C2 M <->
    putnam_1996_a2_solution O1 O2 M.
Admitted.
