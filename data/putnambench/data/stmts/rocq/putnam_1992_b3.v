(* Statement-only formalization of PutnamBench artifact putnam_1992_b3:
   the planar Lebesgue area of the real pairs whose recursively defined
   sequence converges is 4 + pi. This file contains no proof. *)

From Stdlib Require Import Reals SeqSeries.

Open Scope R_scope.

Definition putnam_1992_b3_point : Type := (R * R)%type.

Definition putnam_1992_b3_point_set : Type :=
  putnam_1992_b3_point -> Prop.

Record putnam_1992_b3_open_rectangle : Type := {
  putnam_1992_b3_x_lower : R;
  putnam_1992_b3_x_upper : R;
  putnam_1992_b3_y_lower : R;
  putnam_1992_b3_y_upper : R
}.

Definition putnam_1992_b3_in_open_rectangle
    (rectangle : putnam_1992_b3_open_rectangle)
    (p : putnam_1992_b3_point) : Prop :=
  putnam_1992_b3_x_lower rectangle < fst p <
    putnam_1992_b3_x_upper rectangle /\
  putnam_1992_b3_y_lower rectangle < snd p <
    putnam_1992_b3_y_upper rectangle.

Definition putnam_1992_b3_rectangle_area
    (rectangle : putnam_1992_b3_open_rectangle) : R :=
  Rmax 0
    (putnam_1992_b3_x_upper rectangle -
     putnam_1992_b3_x_lower rectangle) *
  Rmax 0
    (putnam_1992_b3_y_upper rectangle -
     putnam_1992_b3_y_lower rectangle).

Definition putnam_1992_b3_rectangles_cover
    (A : putnam_1992_b3_point_set)
    (rectangles : nat -> putnam_1992_b3_open_rectangle) : Prop :=
  forall p : putnam_1992_b3_point,
    A p ->
    exists n : nat,
      putnam_1992_b3_in_open_rectangle (rectangles n) p.

Fixpoint putnam_1992_b3_partial_rectangle_area
    (rectangles : nat -> putnam_1992_b3_open_rectangle)
    (n : nat) : R :=
  match n with
  | O => 0
  | S k =>
      putnam_1992_b3_partial_rectangle_area rectangles k +
      putnam_1992_b3_rectangle_area (rectangles k)
  end.

(* Equality with finite planar Lebesgue outer measure, expressed through
   countable open-rectangle covers. *)
Definition putnam_1992_b3_has_planar_lebesgue_measure
    (A : putnam_1992_b3_point_set) (area : R) : Prop :=
  0 <= area /\
  (forall rectangles : nat -> putnam_1992_b3_open_rectangle,
    putnam_1992_b3_rectangles_cover A rectangles ->
    forall lower : R,
      lower < area ->
      exists n : nat,
        lower <
        putnam_1992_b3_partial_rectangle_area rectangles n) /\
  (forall epsilon : R,
    0 < epsilon ->
    exists rectangles : nat -> putnam_1992_b3_open_rectangle,
      putnam_1992_b3_rectangles_cover A rectangles /\
      forall n : nat,
        putnam_1992_b3_partial_rectangle_area rectangles n <
        area + epsilon).

Definition putnam_1992_b3_convergence_region
    (a : putnam_1992_b3_point -> nat -> R)
    : putnam_1992_b3_point_set :=
  fun p : putnam_1992_b3_point =>
    exists L : R, Un_cv (a p) L.

Definition putnam_1992_b3_solution : R := 4 + PI.

Theorem putnam_1992_b3
    (a : putnam_1992_b3_point -> nat -> R)
    (ha :
      forall p : putnam_1992_b3_point,
        a p O = fst p /\
        forall n : nat,
          a p (S n) =
          ((a p n) ^ 2 + (snd p) ^ 2) / 2) :
  putnam_1992_b3_has_planar_lebesgue_measure
    (putnam_1992_b3_convergence_region a)
    putnam_1992_b3_solution.
Admitted.
