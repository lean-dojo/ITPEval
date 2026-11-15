(* Statement-only formalization of PutnamBench corpus artifact putnam_2006_b1:
   the cubic curve x^3 + 3xy + y^3 = 1 contains a unique three-point
   equilateral triangle, whose convex hull has area 3 * sqrt(3) / 2.
   This file contains no proof. *)

From Stdlib Require Import Reals List.

Open Scope R_scope.

Definition point := (R * R)%type.
Definition point_set := point -> Prop.

Definition putnam_2006_b1_curve : point_set :=
  fun p : point =>
    fst p ^ 3 + 3 * fst p * snd p + snd p ^ 3 = 1.

Definition putnam_2006_b1_distance (p q : point) : R :=
  sqrt ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2).

Definition putnam_2006_b1_subset
    (A B : point_set) : Prop :=
  forall p : point, A p -> B p.

Definition putnam_2006_b1_same_set
    (A B : point_set) : Prop :=
  forall p : point, A p <-> B p.

Definition putnam_2006_b1_has_cardinality
    (S : point_set) (n : nat) : Prop :=
  exists enumeration : list point,
    NoDup enumeration /\
    length enumeration = n /\
    forall p : point, In p enumeration <-> S p.

Definition putnam_2006_b1_equilateral
    (S : point_set) : Prop :=
  putnam_2006_b1_has_cardinality S 3%nat /\
  exists d : R,
    forall P Q : point,
      S P ->
      S Q ->
      P <> Q ->
      putnam_2006_b1_distance P Q = d.

Definition putnam_2006_b1_affine_combination
    (t : R) (p q : point) : point :=
  ((1 - t) * fst p + t * fst q,
   (1 - t) * snd p + t * snd q).

Definition putnam_2006_b1_convex
    (S : point_set) : Prop :=
  forall (p q : point) (t : R),
    S p ->
    S q ->
    0 <= t <= 1 ->
    S (putnam_2006_b1_affine_combination t p q).

Definition putnam_2006_b1_convex_hull
    (S : point_set) : point_set :=
  fun p : point =>
    forall C : point_set,
      putnam_2006_b1_convex C ->
      putnam_2006_b1_subset S C ->
      C p.

Record putnam_2006_b1_open_rectangle : Type := {
  putnam_2006_b1_x_lower : R;
  putnam_2006_b1_x_upper : R;
  putnam_2006_b1_y_lower : R;
  putnam_2006_b1_y_upper : R
}.

Definition putnam_2006_b1_in_open_rectangle
    (rectangle : putnam_2006_b1_open_rectangle)
    (p : point) : Prop :=
  putnam_2006_b1_x_lower rectangle < fst p <
    putnam_2006_b1_x_upper rectangle /\
  putnam_2006_b1_y_lower rectangle < snd p <
    putnam_2006_b1_y_upper rectangle.

Definition putnam_2006_b1_rectangle_area
    (rectangle : putnam_2006_b1_open_rectangle) : R :=
  Rmax 0
    (putnam_2006_b1_x_upper rectangle -
     putnam_2006_b1_x_lower rectangle) *
  Rmax 0
    (putnam_2006_b1_y_upper rectangle -
     putnam_2006_b1_y_lower rectangle).

Definition putnam_2006_b1_rectangles_cover
    (S : point_set)
    (rectangles : nat -> putnam_2006_b1_open_rectangle) : Prop :=
  forall p : point,
    S p ->
    exists n : nat,
      putnam_2006_b1_in_open_rectangle (rectangles n) p.

Fixpoint putnam_2006_b1_partial_rectangle_area
    (rectangles : nat -> putnam_2006_b1_open_rectangle)
    (n : nat) : R :=
  match n with
  | O => 0
  | S k =>
      putnam_2006_b1_partial_rectangle_area rectangles k +
      putnam_2006_b1_rectangle_area (rectangles k)
  end.

(* The countable-open-rectangle characterization of planar Lebesgue outer
   measure, which equals Lebesgue measure on this finite convex hull. *)
Definition putnam_2006_b1_has_planar_lebesgue_measure
    (S : point_set) (area : R) : Prop :=
  0 <= area /\
  (forall rectangles : nat -> putnam_2006_b1_open_rectangle,
    putnam_2006_b1_rectangles_cover S rectangles ->
    forall lower : R,
      lower < area ->
      exists n : nat,
        lower <
          putnam_2006_b1_partial_rectangle_area rectangles n) /\
  (forall epsilon : R,
    0 < epsilon ->
    exists rectangles : nat -> putnam_2006_b1_open_rectangle,
      putnam_2006_b1_rectangles_cover S rectangles /\
      forall n : nat,
        putnam_2006_b1_partial_rectangle_area rectangles n <
          area + epsilon).

Definition putnam_2006_b1_solution : R :=
  3 * sqrt 3 / 2.

Definition putnam_2006_b1_unique_triangle : Prop :=
  exists S : point_set,
    putnam_2006_b1_subset S putnam_2006_b1_curve /\
    putnam_2006_b1_equilateral S /\
    forall T : point_set,
      putnam_2006_b1_subset T putnam_2006_b1_curve /\
      putnam_2006_b1_equilateral T ->
      putnam_2006_b1_same_set T S.

Theorem putnam_2006_b1 :
  putnam_2006_b1_unique_triangle /\
  exists S : point_set,
    putnam_2006_b1_subset S putnam_2006_b1_curve /\
    putnam_2006_b1_equilateral S /\
    putnam_2006_b1_has_planar_lebesgue_measure
      (putnam_2006_b1_convex_hull S)
      putnam_2006_b1_solution.
Admitted.
