(* Statement-only formalization of PutnamBench corpus artifact putnam_1993_b3:
   the planar probability that the nearest integer to x/y is even for
   uniformly chosen x,y in the open unit interval. This file contains no
   proof. *)

From Stdlib Require Import Reals ZArith QArith.

Open Scope R_scope.

Definition putnam_1993_b3_point := (R * R)%type.
Definition putnam_1993_b3_point_set := putnam_1993_b3_point -> Prop.

Definition putnam_1993_b3_solution : (Q * Q)%type :=
  ((5 / 4)%Q, (-1 / 4)%Q).

Definition putnam_1993_b3_nearest_integer (t : R) : Z :=
  Int_part (t + 1 / 2).

Definition putnam_1993_b3_event : putnam_1993_b3_point_set :=
  fun p : putnam_1993_b3_point =>
    0 < fst p /\
    fst p < 1 /\
    0 < snd p /\
    snd p < 1 /\
    Z.even
      (putnam_1993_b3_nearest_integer (fst p / snd p)) = true.

Record putnam_1993_b3_open_rectangle : Type := {
  putnam_1993_b3_x_lower : R;
  putnam_1993_b3_x_upper : R;
  putnam_1993_b3_y_lower : R;
  putnam_1993_b3_y_upper : R
}.

Definition putnam_1993_b3_in_open_rectangle
    (rectangle : putnam_1993_b3_open_rectangle)
    (p : putnam_1993_b3_point) : Prop :=
  putnam_1993_b3_x_lower rectangle < fst p <
    putnam_1993_b3_x_upper rectangle /\
  putnam_1993_b3_y_lower rectangle < snd p <
    putnam_1993_b3_y_upper rectangle.

Definition putnam_1993_b3_rectangle_area
    (rectangle : putnam_1993_b3_open_rectangle) : R :=
  Rmax 0
    (putnam_1993_b3_x_upper rectangle -
     putnam_1993_b3_x_lower rectangle) *
  Rmax 0
    (putnam_1993_b3_y_upper rectangle -
     putnam_1993_b3_y_lower rectangle).

Definition putnam_1993_b3_rectangles_cover
    (S : putnam_1993_b3_point_set)
    (rectangles : nat -> putnam_1993_b3_open_rectangle) : Prop :=
  forall p : putnam_1993_b3_point,
    S p ->
    exists n : nat,
      putnam_1993_b3_in_open_rectangle (rectangles n) p.

Fixpoint putnam_1993_b3_partial_rectangle_area
    (rectangles : nat -> putnam_1993_b3_open_rectangle)
    (n : nat) : R :=
  match n with
  | O => 0
  | S k =>
      putnam_1993_b3_partial_rectangle_area rectangles k +
      putnam_1993_b3_rectangle_area (rectangles k)
  end.

(* The countable-open-rectangle characterization of finite planar Lebesgue
   outer measure, equal here to Lebesgue measure because the event is Borel. *)
Definition putnam_1993_b3_has_planar_lebesgue_measure
    (S : putnam_1993_b3_point_set) (area : R) : Prop :=
  0 <= area /\
  (forall rectangles : nat -> putnam_1993_b3_open_rectangle,
    putnam_1993_b3_rectangles_cover S rectangles ->
    forall lower : R,
      lower < area ->
      exists n : nat,
        lower <
          putnam_1993_b3_partial_rectangle_area rectangles n) /\
  (forall epsilon : R,
    0 < epsilon ->
    exists rectangles : nat -> putnam_1993_b3_open_rectangle,
      putnam_1993_b3_rectangles_cover S rectangles /\
      forall n : nat,
        putnam_1993_b3_partial_rectangle_area rectangles n <
          area + epsilon).

Theorem putnam_1993_b3 :
  putnam_1993_b3_has_planar_lebesgue_measure
    putnam_1993_b3_event
    (Q2R (fst putnam_1993_b3_solution) +
     Q2R (snd putnam_1993_b3_solution) * PI).
Admitted.
