(* Statement-only formalization of PutnamBench artifact putnam_1979_b5:
   a closed convex planar set containing no nonzero lattice point and having
   equal area in the four quadrants has area at most four. This file contains
   no proof. *)

From Stdlib Require Import Reals ZArith.

Open Scope R_scope.

Definition point := (R * R)%type.
Definition point_set := point -> Prop.

Definition point_distance (p q : point) : R :=
  sqrt ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2).

Definition affine_combination (t : R) (p q : point) : point :=
  ((1 - t) * fst p + t * fst q,
   (1 - t) * snd p + t * snd q).

Definition closed (S : point_set) : Prop :=
  forall p : point,
    ~ S p ->
    exists epsilon : R,
      0 < epsilon /\
      forall q : point,
        point_distance p q < epsilon ->
        ~ S q.

Definition convex (S : point_set) : Prop :=
  forall (p q : point) (t : R),
    S p ->
    S q ->
    0 <= t <= 1 ->
    S (affine_combination t p q).

Definition intersection (A B : point_set) : point_set :=
  fun p : point => A p /\ B p.

Definition quadrant_pp : point_set :=
  fun p : point => 0 <= fst p /\ 0 <= snd p.

Definition quadrant_pn : point_set :=
  fun p : point => 0 <= fst p /\ snd p <= 0.

Definition quadrant_np : point_set :=
  fun p : point => fst p <= 0 /\ 0 <= snd p.

Definition quadrant_nn : point_set :=
  fun p : point => fst p <= 0 /\ snd p <= 0.

Record open_rectangle : Type := {
  rectangle_x_lower : R;
  rectangle_x_upper : R;
  rectangle_y_lower : R;
  rectangle_y_upper : R
}.

Definition in_open_rectangle
    (rectangle : open_rectangle) (p : point) : Prop :=
  rectangle_x_lower rectangle < fst p <
    rectangle_x_upper rectangle /\
  rectangle_y_lower rectangle < snd p <
    rectangle_y_upper rectangle.

Definition rectangle_area (rectangle : open_rectangle) : R :=
  Rmax 0
    (rectangle_x_upper rectangle - rectangle_x_lower rectangle) *
  Rmax 0
    (rectangle_y_upper rectangle - rectangle_y_lower rectangle).

Definition rectangles_cover
    (S : point_set) (rectangles : nat -> open_rectangle) : Prop :=
  forall p : point,
    S p ->
    exists n : nat, in_open_rectangle (rectangles n) p.

Fixpoint partial_rectangle_area
    (rectangles : nat -> open_rectangle) (n : nat) : R :=
  match n with
  | O => 0
  | S k =>
      partial_rectangle_area rectangles k +
      rectangle_area (rectangles k)
  end.

(* This is the countable-open-rectangle characterization of an upper bound
   for planar Lebesgue outer measure. *)
Definition planar_lebesgue_measure_at_most
    (S : point_set) (bound : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists rectangles : nat -> open_rectangle,
      rectangles_cover S rectangles /\
      forall n : nat,
        partial_rectangle_area rectangles n < bound + epsilon.

(* Equality of all real upper cuts also covers the case of infinite measure. *)
Definition same_planar_lebesgue_measure
    (A B : point_set) : Prop :=
  forall bound : R,
    planar_lebesgue_measure_at_most A bound <->
    planar_lebesgue_measure_at_most B bound.

Theorem putnam_1979_b5
    (C : point_set)
    (hC :
      closed C /\
      convex C /\
      C (0, 0))
    (hCnint :
      forall a b : Z,
        (a <> 0%Z \/ b <> 0%Z) ->
        ~ C (IZR a, IZR b))
    (hCeven :
      same_planar_lebesgue_measure
        (intersection C quadrant_pp)
        (intersection C quadrant_pn) /\
      same_planar_lebesgue_measure
        (intersection C quadrant_pn)
        (intersection C quadrant_np) /\
      same_planar_lebesgue_measure
        (intersection C quadrant_np)
        (intersection C quadrant_nn)) :
  planar_lebesgue_measure_at_most C 4.
Admitted.
