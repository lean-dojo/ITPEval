(* Statement-only formalization of PutnamBench artifact putnam_1967_a5:
   a convex region in the Euclidean plane with area greater than pi/4
   contains two points exactly one unit apart. This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition point := (R * R)%type.
Definition point_set := point -> Prop.

Definition affine_combination (t : R) (p q : point) : point :=
  ((1 - t) * fst p + t * fst q,
   (1 - t) * snd p + t * snd q).

Definition convex (S : point_set) : Prop :=
  forall (p q : point) (t : R),
    S p ->
    S q ->
    0 <= t <= 1 ->
    S (affine_combination t p q).

Definition point_distance (p q : point) : R :=
  sqrt ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2).

Record open_rectangle := {
  x_lower : R;
  x_upper : R;
  y_lower : R;
  y_upper : R
}.

Definition in_open_rectangle
    (rectangle : open_rectangle) (p : point) : Prop :=
  x_lower rectangle < fst p < x_upper rectangle /\
  y_lower rectangle < snd p < y_upper rectangle.

Definition rectangle_area (rectangle : open_rectangle) : R :=
  Rmax 0 (x_upper rectangle - x_lower rectangle) *
  Rmax 0 (y_upper rectangle - y_lower rectangle).

Definition rectangles_cover
    (S : point_set) (rectangles : nat -> open_rectangle) : Prop :=
  forall p : point,
    S p ->
    exists n : nat, in_open_rectangle (rectangles n) p.

Fixpoint partial_area
    (rectangles : nat -> open_rectangle) (n : nat) : R :=
  match n with
  | O => 0
  | S k => partial_area rectangles k + rectangle_area (rectangles k)
  end.

(* A strict lower bound for planar Lebesgue outer measure, expressed through
   the sums of all countable open-rectangle covers. *)
Definition planar_outer_measure_greater_than
    (S : point_set) (bound : R) : Prop :=
  exists lower : R,
    bound < lower /\
    forall rectangles : nat -> open_rectangle,
      rectangles_cover S rectangles ->
      forall b : R,
        b < lower ->
        exists n : nat, b < partial_area rectangles n.

Theorem putnam_1967_a5 :
  forall S : point_set,
    convex S /\ planar_outer_measure_greater_than S (PI / 4) ->
    exists P Q : point,
      S P /\ S Q /\ point_distance P Q = 1.
Admitted.
