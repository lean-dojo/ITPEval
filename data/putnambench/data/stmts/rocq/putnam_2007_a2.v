(* Statement-only formalization of PutnamBench corpus artifact putnam_2007_a2:
   four is the least planar Lebesgue area of a convex set meeting both
   branches of each hyperbola xy = 1 and xy = -1; this file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_2007_a2_point := (R * R)%type.
Definition putnam_2007_a2_point_set := putnam_2007_a2_point -> Prop.

Definition putnam_2007_a2_affine_combination
    (t : R) (p q : putnam_2007_a2_point) : putnam_2007_a2_point :=
  ((1 - t) * fst p + t * fst q,
   (1 - t) * snd p + t * snd q).

Definition putnam_2007_a2_convex
    (S : putnam_2007_a2_point_set) : Prop :=
  forall (p q : putnam_2007_a2_point) (t : R),
    S p ->
    S q ->
    0 <= t <= 1 ->
    S (putnam_2007_a2_affine_combination t p q).

Definition putnam_2007_a2_admissible
    (S : putnam_2007_a2_point_set) : Prop :=
  putnam_2007_a2_convex S /\
  (exists p : putnam_2007_a2_point,
    S p /\ 0 < fst p /\ 0 < snd p /\ fst p * snd p = 1) /\
  (exists p : putnam_2007_a2_point,
    S p /\ fst p < 0 /\ snd p < 0 /\ fst p * snd p = 1) /\
  (exists p : putnam_2007_a2_point,
    S p /\ fst p < 0 /\ 0 < snd p /\ fst p * snd p = -1) /\
  (exists p : putnam_2007_a2_point,
    S p /\ 0 < fst p /\ snd p < 0 /\ fst p * snd p = -1).

Record putnam_2007_a2_open_rectangle : Type := {
  putnam_2007_a2_x_lower : R;
  putnam_2007_a2_x_upper : R;
  putnam_2007_a2_y_lower : R;
  putnam_2007_a2_y_upper : R
}.

Definition putnam_2007_a2_in_open_rectangle
    (rectangle : putnam_2007_a2_open_rectangle)
    (p : putnam_2007_a2_point) : Prop :=
  putnam_2007_a2_x_lower rectangle < fst p <
    putnam_2007_a2_x_upper rectangle /\
  putnam_2007_a2_y_lower rectangle < snd p <
    putnam_2007_a2_y_upper rectangle.

Definition putnam_2007_a2_rectangle_area
    (rectangle : putnam_2007_a2_open_rectangle) : R :=
  Rmax 0
    (putnam_2007_a2_x_upper rectangle -
     putnam_2007_a2_x_lower rectangle) *
  Rmax 0
    (putnam_2007_a2_y_upper rectangle -
     putnam_2007_a2_y_lower rectangle).

Definition putnam_2007_a2_rectangles_cover
    (S : putnam_2007_a2_point_set)
    (rectangles : nat -> putnam_2007_a2_open_rectangle) : Prop :=
  forall p : putnam_2007_a2_point,
    S p ->
    exists n : nat,
      putnam_2007_a2_in_open_rectangle (rectangles n) p.

Fixpoint putnam_2007_a2_partial_rectangle_area
    (rectangles : nat -> putnam_2007_a2_open_rectangle)
    (n : nat) : R :=
  match n with
  | O => 0
  | S k =>
      putnam_2007_a2_partial_rectangle_area rectangles k +
      putnam_2007_a2_rectangle_area (rectangles k)
  end.

(* The countable-open-rectangle characterization of finite planar Lebesgue
   outer measure. *)
Definition putnam_2007_a2_has_planar_lebesgue_measure
    (S : putnam_2007_a2_point_set) (area : R) : Prop :=
  0 <= area /\
  (forall rectangles : nat -> putnam_2007_a2_open_rectangle,
    putnam_2007_a2_rectangles_cover S rectangles ->
    forall lower : R,
      lower < area ->
      exists n : nat,
        lower <
          putnam_2007_a2_partial_rectangle_area rectangles n) /\
  (forall epsilon : R,
    0 < epsilon ->
    exists rectangles : nat -> putnam_2007_a2_open_rectangle,
      putnam_2007_a2_rectangles_cover S rectangles /\
      forall n : nat,
        putnam_2007_a2_partial_rectangle_area rectangles n <
          area + epsilon).

Definition putnam_2007_a2_is_least_possible_area (area : R) : Prop :=
  (exists S : putnam_2007_a2_point_set,
    putnam_2007_a2_admissible S /\
    putnam_2007_a2_has_planar_lebesgue_measure S area) /\
  (forall (S : putnam_2007_a2_point_set) (candidate_area : R),
    putnam_2007_a2_admissible S ->
    putnam_2007_a2_has_planar_lebesgue_measure S candidate_area ->
    area <= candidate_area).

Theorem putnam_2007_a2 :
  putnam_2007_a2_is_least_possible_area 4.
Admitted.
