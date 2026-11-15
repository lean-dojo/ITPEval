(*
  Statement-only formalization of Hundred Theorems artifact 008,
  "The Impossibility of Trisecting the Angle and Doubling the Cube".
  It states that, in the straightedge-and-compass construction closure
  generated from rational points, doubling the cube and trisecting a
  60-degree angle are impossible. This file contains no proof.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Rtrigo1.
From Stdlib Require Import ZArith.

Open Scope R_scope.

Record point : Type := Point {
  abscissa : R;
  ordinate : R
}.

Definition is_rational (x : R) : Prop :=
  exists p q : Z, q <> 0%Z /\ x = IZR p / IZR q.

Definition point_distance (a b : point) : R :=
  sqrt ((abscissa b - abscissa a) ^ 2 +
        (ordinate b - ordinate a) ^ 2).

Definition lines_parallel (a b c d : point) : Prop :=
  (abscissa b - abscissa a) * (ordinate d - ordinate c) =
  (ordinate b - ordinate a) * (abscissa d - abscissa c).

Definition collinear (a p b : point) : Prop :=
  lines_parallel a b a p.

Definition is_intersection (p a b c d : point) : Prop :=
  collinear a p b /\ collinear c p d.

Inductive constructible : point -> Prop :=
| constructible_rational :
    forall p,
      is_rational (abscissa p) ->
      is_rational (ordinate p) ->
      constructible p
| constructible_line_line :
    forall a b c d p,
      constructible a ->
      constructible b ->
      constructible c ->
      constructible d ->
      ~ lines_parallel a b c d ->
      is_intersection p a b c d ->
      constructible p
| constructible_line_circle :
    forall a b c d e p,
      constructible a ->
      constructible b ->
      constructible c ->
      constructible d ->
      constructible e ->
      a <> b ->
      collinear a p b ->
      point_distance c p = point_distance d e ->
      constructible p
| constructible_circle_circle :
    forall a b c d e f p,
      constructible a ->
      constructible b ->
      constructible c ->
      constructible d ->
      constructible e ->
      constructible f ->
      ~ (a = d /\ point_distance b c = point_distance e f) ->
      point_distance a p = point_distance b c ->
      point_distance d p = point_distance e f ->
      constructible p.

Theorem impossibility_of_doubling_the_cube :
  forall x : R,
    x ^ 3 = 2 ->
    ~ constructible (Point x 0).
Admitted.

Theorem impossibility_of_trisecting_the_angle :
  forall y : R,
    ~ constructible (Point (cos (PI / 9)) y).
Admitted.
