(* Statement-only formalization of PutnamBench corpus artifact putnam_2024_a5:
   the center displacement that minimizes the probability that the full line
   through two random points on the radius-9 circle meets the unit sphere.
   This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_2024_a5_point : Type := (R * R)%type.
Definition putnam_2024_a5_point_set : Type :=
  putnam_2024_a5_point -> Prop.

Definition putnam_2024_a5_affine_combination
    (u : R) (P Q : putnam_2024_a5_point) :
    putnam_2024_a5_point :=
  ((1 - u) * fst P + u * fst Q,
   (1 - u) * snd P + u * snd Q).

Definition putnam_2024_a5_squared_distance
    (P Q : putnam_2024_a5_point) : R :=
  (fst P - fst Q) ^ 2 + (snd P - snd Q) ^ 2.

Definition putnam_2024_a5_circle_point
    (s : R) : putnam_2024_a5_point :=
  (9 * cos (2 * PI * s), 9 * sin (2 * PI * s)).

Definition putnam_2024_a5_line_intersects_sphere
    (r : R) (P Q : putnam_2024_a5_point) : Prop :=
  exists u : R,
    putnam_2024_a5_squared_distance
      (putnam_2024_a5_affine_combination u P Q) (r, 0) = 1.

Definition putnam_2024_a5_event
    (IsIntersecting :
      R -> putnam_2024_a5_point -> putnam_2024_a5_point -> Prop)
    (r : R) : putnam_2024_a5_point_set :=
  fun st : putnam_2024_a5_point =>
    0 <= fst st <= 1 /\
    0 <= snd st <= 1 /\
    IsIntersecting r
      (putnam_2024_a5_circle_point (fst st))
      (putnam_2024_a5_circle_point (snd st)).

Record putnam_2024_a5_open_rectangle : Type := {
  putnam_2024_a5_x_lower : R;
  putnam_2024_a5_x_upper : R;
  putnam_2024_a5_y_lower : R;
  putnam_2024_a5_y_upper : R
}.

Definition putnam_2024_a5_in_open_rectangle
    (rectangle : putnam_2024_a5_open_rectangle)
    (p : putnam_2024_a5_point) : Prop :=
  putnam_2024_a5_x_lower rectangle < fst p <
    putnam_2024_a5_x_upper rectangle /\
  putnam_2024_a5_y_lower rectangle < snd p <
    putnam_2024_a5_y_upper rectangle.

Definition putnam_2024_a5_rectangle_area
    (rectangle : putnam_2024_a5_open_rectangle) : R :=
  Rmax 0
    (putnam_2024_a5_x_upper rectangle -
     putnam_2024_a5_x_lower rectangle) *
  Rmax 0
    (putnam_2024_a5_y_upper rectangle -
     putnam_2024_a5_y_lower rectangle).

Definition putnam_2024_a5_rectangles_cover
    (S : putnam_2024_a5_point_set)
    (rectangles : nat -> putnam_2024_a5_open_rectangle) : Prop :=
  forall p : putnam_2024_a5_point,
    S p ->
    exists n : nat,
      putnam_2024_a5_in_open_rectangle (rectangles n) p.

Fixpoint putnam_2024_a5_partial_rectangle_area
    (rectangles : nat -> putnam_2024_a5_open_rectangle)
    (n : nat) : R :=
  match n with
  | O => 0
  | S k =>
      putnam_2024_a5_partial_rectangle_area rectangles k +
      putnam_2024_a5_rectangle_area (rectangles k)
  end.

(* This is the countable-open-rectangle characterization of finite planar
   Lebesgue outer measure. For this closed event it equals Lebesgue measure;
   on the unit parameter square that area is the required probability. *)
Definition putnam_2024_a5_has_planar_lebesgue_measure
    (S : putnam_2024_a5_point_set) (area : R) : Prop :=
  0 <= area /\
  (forall rectangles : nat -> putnam_2024_a5_open_rectangle,
    putnam_2024_a5_rectangles_cover S rectangles ->
    forall lower : R,
      lower < area ->
      exists n : nat,
        lower <
          putnam_2024_a5_partial_rectangle_area rectangles n) /\
  (forall epsilon : R,
    0 < epsilon ->
    exists rectangles : nat -> putnam_2024_a5_open_rectangle,
      putnam_2024_a5_rectangles_cover S rectangles /\
      forall n : nat,
        putnam_2024_a5_partial_rectangle_area rectangles n <
          area + epsilon).

Definition putnam_2024_a5_solution (r : R) : Prop :=
  r = 0.

Theorem putnam_2024_a5
    (IsIntersecting :
      R -> putnam_2024_a5_point -> putnam_2024_a5_point -> Prop)
    (IsIntersecting_def :
      forall (r : R) (P Q : putnam_2024_a5_point),
        IsIntersecting r P Q <->
        putnam_2024_a5_line_intersects_sphere r P Q)
    (ProbIntersect : R -> R)
    (ProbIntersect_def :
      forall r : R,
        putnam_2024_a5_has_planar_lebesgue_measure
          (putnam_2024_a5_event IsIntersecting r)
          (ProbIntersect r)) :
  forall r : R,
    (0 <= r <= 8 /\
     forall x : R, 0 <= x <= 8 -> ProbIntersect r <= ProbIntersect x) <->
    putnam_2024_a5_solution r.
Admitted.
