(* Statement-only formalization of PutnamBench corpus artifact putnam_1988_a1:
   the planar Lebesgue area of the region satisfying
   |x| - |y| <= 1 and |y| <= 1 is 6; this file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition point := (R * R)%type.
Definition point_set := point -> Prop.

Definition same_set (A B : point_set) : Prop :=
  forall p : point, A p <-> B p.

Definition putnam_1988_a1_region : point_set :=
  fun p : point =>
    Rabs (fst p) - Rabs (snd p) <= 1 /\
    Rabs (snd p) <= 1.

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
    (A : point_set) (rectangles : nat -> open_rectangle) : Prop :=
  forall p : point,
    A p ->
    exists n : nat, in_open_rectangle (rectangles n) p.

Fixpoint partial_rectangle_area
    (rectangles : nat -> open_rectangle) (n : nat) : R :=
  match n with
  | O => 0
  | S k =>
      partial_rectangle_area rectangles k +
      rectangle_area (rectangles k)
  end.

(* The countable-open-rectangle characterization of finite planar Lebesgue
   outer measure; on this closed region it is planar Lebesgue measure. *)
Definition has_planar_lebesgue_measure
    (A : point_set) (area : R) : Prop :=
  0 <= area /\
  (forall rectangles : nat -> open_rectangle,
    rectangles_cover A rectangles ->
    forall lower : R,
      lower < area ->
      exists n : nat,
        lower < partial_rectangle_area rectangles n) /\
  (forall epsilon : R,
    0 < epsilon ->
    exists rectangles : nat -> open_rectangle,
      rectangles_cover A rectangles /\
      forall n : nat,
        partial_rectangle_area rectangles n < area + epsilon).

Definition putnam_1988_a1_solution : R := 6.

Theorem putnam_1988_a1
    (region : point_set)
    (hregion : same_set region putnam_1988_a1_region) :
  has_planar_lebesgue_measure region putnam_1988_a1_solution.
Admitted.
