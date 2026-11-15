(* Statement-only formalization of PutnamBench corpus artifact putnam_1998_a2:
   for a first-quadrant unit-circle arc, the sum of the area below the arc and
   the area between the y-axis and the arc depends only on its angular length.
   This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_1998_a2_point : Type := (R * R)%type.
Definition putnam_1998_a2_point_set : Type :=
  putnam_1998_a2_point -> Prop.

Definition putnam_1998_a2_distance
    (p q : putnam_1998_a2_point) : R :=
  sqrt ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2).

Record putnam_1998_a2_open_rectangle : Type := {
  putnam_1998_a2_x_lower : R;
  putnam_1998_a2_x_upper : R;
  putnam_1998_a2_y_lower : R;
  putnam_1998_a2_y_upper : R
}.

Definition putnam_1998_a2_in_open_rectangle
    (rectangle : putnam_1998_a2_open_rectangle)
    (p : putnam_1998_a2_point) : Prop :=
  putnam_1998_a2_x_lower rectangle < fst p <
    putnam_1998_a2_x_upper rectangle /\
  putnam_1998_a2_y_lower rectangle < snd p <
    putnam_1998_a2_y_upper rectangle.

Definition putnam_1998_a2_rectangle_area
    (rectangle : putnam_1998_a2_open_rectangle) : R :=
  Rmax 0
    (putnam_1998_a2_x_upper rectangle -
     putnam_1998_a2_x_lower rectangle) *
  Rmax 0
    (putnam_1998_a2_y_upper rectangle -
     putnam_1998_a2_y_lower rectangle).

Definition putnam_1998_a2_rectangles_cover
    (region : putnam_1998_a2_point_set)
    (rectangles : nat -> putnam_1998_a2_open_rectangle) : Prop :=
  forall p : putnam_1998_a2_point,
    region p ->
    exists n : nat,
      putnam_1998_a2_in_open_rectangle (rectangles n) p.

Fixpoint putnam_1998_a2_partial_rectangle_area
    (rectangles : nat -> putnam_1998_a2_open_rectangle)
    (n : nat) : R :=
  match n with
  | O => 0
  | S k =>
      putnam_1998_a2_partial_rectangle_area rectangles k +
      putnam_1998_a2_rectangle_area (rectangles k)
  end.

(* Equality with finite planar Lebesgue outer measure, expressed through
   countable open-rectangle covers. *)
Definition putnam_1998_a2_has_planar_lebesgue_measure
    (region : putnam_1998_a2_point_set) (area : R) : Prop :=
  0 <= area /\
  (forall rectangles : nat -> putnam_1998_a2_open_rectangle,
    putnam_1998_a2_rectangles_cover region rectangles ->
    forall lower : R,
      lower < area ->
      exists n : nat,
        lower <
        putnam_1998_a2_partial_rectangle_area rectangles n) /\
  (forall epsilon : R,
    0 < epsilon ->
    exists rectangles : nat -> putnam_1998_a2_open_rectangle,
      putnam_1998_a2_rectangles_cover region rectangles /\
      forall n : nat,
        putnam_1998_a2_partial_rectangle_area rectangles n <
        area + epsilon).

Theorem putnam_1998_a2
    (quadrant : putnam_1998_a2_point -> Prop)
    (isarc :
      putnam_1998_a2_point -> putnam_1998_a2_point -> Prop)
    (arc :
      putnam_1998_a2_point -> putnam_1998_a2_point ->
      putnam_1998_a2_point_set)
    (A B :
      putnam_1998_a2_point -> putnam_1998_a2_point -> R)
    (hquadrant :
      forall P : putnam_1998_a2_point,
        quadrant P <->
        fst P > 0 /\
        snd P > 0 /\
        putnam_1998_a2_distance (0, 0) P = 1)
    (hisarc :
      forall P Q : putnam_1998_a2_point,
        isarc P Q <->
        quadrant P /\ quadrant Q /\ fst P > fst Q)
    (harc :
      forall P Q R : putnam_1998_a2_point,
        arc P Q R <->
        quadrant R /\ fst P > fst R /\ fst R > fst Q)
    (hA :
      forall P Q : putnam_1998_a2_point,
        putnam_1998_a2_has_planar_lebesgue_measure
          (fun S : putnam_1998_a2_point =>
            exists R : putnam_1998_a2_point,
              arc P Q R /\
              fst R = fst S /\
              snd R > snd S /\
              snd S > 0)
          (A P Q))
    (hB :
      forall P Q : putnam_1998_a2_point,
        putnam_1998_a2_has_planar_lebesgue_measure
          (fun S : putnam_1998_a2_point =>
            exists R : putnam_1998_a2_point,
              arc P Q R /\
              snd R = snd S /\
              fst R > fst S /\
              fst S > 0)
          (B P Q)) :
  exists f : R -> R,
    forall P Q : putnam_1998_a2_point,
      isarc P Q ->
      A P Q + B P Q =
      f (atan (snd Q / fst Q) - atan (snd P / fst P)).
Admitted.
