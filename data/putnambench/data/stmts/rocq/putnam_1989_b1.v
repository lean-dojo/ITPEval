(* Statement-only formalization of PutnamBench artifact putnam_1989_b1:
   the planar area probability that a point of the unit square is closer to
   its center than to every boundary point, expressed in normalized quadratic
   irrational form. This file contains no proof. *)

From Stdlib Require Import Reals ZArith ClassicalEpsilon.

Local Open Scope R_scope.

Definition putnam_1989_b1_point := (R * R)%type.
Definition putnam_1989_b1_region := putnam_1989_b1_point -> Prop.

Definition putnam_1989_b1_distance
    (p q : putnam_1989_b1_point) : R :=
  sqrt ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2).

Definition putnam_1989_b1_square : putnam_1989_b1_region :=
  fun p =>
    0 <= fst p <= 1 /\
    0 <= snd p <= 1.

Definition putnam_1989_b1_boundary : putnam_1989_b1_region :=
  fun p =>
    putnam_1989_b1_square p /\
    (fst p = 0 \/ fst p = 1 \/ snd p = 0 \/ snd p = 1).

Definition putnam_1989_b1_center : putnam_1989_b1_point :=
  (1 / 2, 1 / 2).

Definition putnam_1989_b1_closer : putnam_1989_b1_region :=
  fun p =>
    putnam_1989_b1_square p /\
    forall q : putnam_1989_b1_point,
      putnam_1989_b1_boundary q ->
      putnam_1989_b1_distance p putnam_1989_b1_center <
      putnam_1989_b1_distance p q.

Record putnam_1989_b1_open_rectangle := {
  putnam_1989_b1_x_lower : R;
  putnam_1989_b1_x_upper : R;
  putnam_1989_b1_y_lower : R;
  putnam_1989_b1_y_upper : R
}.

Definition putnam_1989_b1_in_open_rectangle
    (rectangle : putnam_1989_b1_open_rectangle)
    (p : putnam_1989_b1_point) : Prop :=
  putnam_1989_b1_x_lower rectangle < fst p <
    putnam_1989_b1_x_upper rectangle /\
  putnam_1989_b1_y_lower rectangle < snd p <
    putnam_1989_b1_y_upper rectangle.

Definition putnam_1989_b1_rectangle_area
    (rectangle : putnam_1989_b1_open_rectangle) : R :=
  Rmax 0
    (putnam_1989_b1_x_upper rectangle -
     putnam_1989_b1_x_lower rectangle) *
  Rmax 0
    (putnam_1989_b1_y_upper rectangle -
     putnam_1989_b1_y_lower rectangle).

Definition putnam_1989_b1_rectangles_cover
    (region : putnam_1989_b1_region)
    (rectangles : nat -> putnam_1989_b1_open_rectangle) : Prop :=
  forall p : putnam_1989_b1_point,
    region p ->
    exists n : nat,
      putnam_1989_b1_in_open_rectangle (rectangles n) p.

Fixpoint putnam_1989_b1_partial_area
    (rectangles : nat -> putnam_1989_b1_open_rectangle)
    (n : nat) : R :=
  match n with
  | O => 0
  | S k =>
      putnam_1989_b1_partial_area rectangles k +
      putnam_1989_b1_rectangle_area (rectangles k)
  end.

Definition putnam_1989_b1_converges_to
    (sequence : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (sequence n - limit) < epsilon.

Definition putnam_1989_b1_cover_cost
    (region : putnam_1989_b1_region) (cost : R) : Prop :=
  exists rectangles : nat -> putnam_1989_b1_open_rectangle,
    putnam_1989_b1_rectangles_cover region rectangles /\
    putnam_1989_b1_converges_to
      (putnam_1989_b1_partial_area rectangles) cost.

Definition putnam_1989_b1_is_outer_area
    (region : putnam_1989_b1_region) (area : R) : Prop :=
  (forall cost : R,
      putnam_1989_b1_cover_cost region cost ->
      area <= cost) /\
  (forall lower_bound : R,
      (forall cost : R,
          putnam_1989_b1_cover_cost region cost ->
          lower_bound <= cost) ->
      lower_bound <= area).

Definition putnam_1989_b1_area
    (region : putnam_1989_b1_region) : R :=
  epsilon (inhabits 0) (putnam_1989_b1_is_outer_area region).

Definition putnam_1989_b1_solution : (Z * Z * Z * Z)%type :=
  (4%Z, 2%Z, (-5)%Z, 3%Z).

Definition putnam_1989_b1_squarefree (b : Z) : Prop :=
  forall n k : Z,
    (b = n * n * k)%Z ->
    (Z.abs n = 1)%Z.

Theorem putnam_1989_b1 :
  let '(a, b, c, d) := putnam_1989_b1_solution in
  (0 < b)%Z /\
  (0 < d)%Z /\
  ~ (exists n : Z, (n * n = b)%Z) /\
  putnam_1989_b1_squarefree b /\
  (Z.gcd (Z.gcd (Z.abs a) (Z.abs c)) (Z.abs d) = 1)%Z /\
  putnam_1989_b1_area putnam_1989_b1_closer /
    putnam_1989_b1_area putnam_1989_b1_square =
    (IZR a * sqrt (IZR b) + IZR c) / IZR d.
Admitted.
