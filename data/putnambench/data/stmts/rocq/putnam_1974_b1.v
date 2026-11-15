(* Statement-only formalization of PutnamBench artifact putnam_1974_b1:
   maximizing the sum of the ten pairwise Euclidean distances among five
   points on the unit circle is equivalent to the cyclic equal-edge
   configuration. This file contains no proof. *)

From Coq Require Import Reals.

Open Scope R_scope.

Definition point := (R * R)%type.

Definition point_distance (a b : point) : R :=
  sqrt ((fst a - fst b) ^ 2 + (snd a - snd b) ^ 2).

Record five_points := {
  point_0 : point;
  point_1 : point;
  point_2 : point;
  point_3 : point;
  point_4 : point
}.

Definition point_at (p : five_points) (i : nat) : point :=
  match i with
  | O => point_0 p
  | S O => point_1 p
  | S (S O) => point_2 p
  | S (S (S O)) => point_3 p
  | S (S (S (S O))) => point_4 p
  | _ => (0, 0)
  end.

Definition on_unit_circle (p : five_points) : Prop :=
  forall i : nat,
    (i < 5)%nat ->
    point_distance (point_at p i) (0, 0) = 1.

Definition total_distance (p : five_points) : R :=
    point_distance (point_0 p) (point_1 p)
  + point_distance (point_0 p) (point_2 p)
  + point_distance (point_0 p) (point_3 p)
  + point_distance (point_0 p) (point_4 p)
  + point_distance (point_1 p) (point_2 p)
  + point_distance (point_1 p) (point_3 p)
  + point_distance (point_1 p) (point_4 p)
  + point_distance (point_2 p) (point_3 p)
  + point_distance (point_2 p) (point_4 p)
  + point_distance (point_3 p) (point_4 p).

Definition permutation_of_five (ordering : nat -> nat) : Prop :=
  (forall i : nat,
      (i < 5)%nat ->
      (ordering i < 5)%nat) /\
  (forall i j : nat,
      (i < 5)%nat ->
      (j < 5)%nat ->
      ordering i = ordering j ->
      i = j) /\
  (forall j : nat,
      (j < 5)%nat ->
      exists i : nat,
        (i < 5)%nat /\ ordering i = j).

Definition points_distinct (p : five_points) : Prop :=
  forall i j : nat,
    (i < 5)%nat ->
    (j < 5)%nat ->
    point_at p i = point_at p j ->
    i = j.

Definition putnam_1974_b1_solution (p : five_points) : Prop :=
  points_distinct p /\
  exists (B : R) (ordering : nat -> nat),
    0 < B /\
    permutation_of_five ordering /\
    point_distance (point_at p (ordering 0%nat))
      (point_at p (ordering 1%nat)) = B /\
    point_distance (point_at p (ordering 1%nat))
      (point_at p (ordering 2%nat)) = B /\
    point_distance (point_at p (ordering 2%nat))
      (point_at p (ordering 3%nat)) = B /\
    point_distance (point_at p (ordering 3%nat))
      (point_at p (ordering 4%nat)) = B /\
    point_distance (point_at p (ordering 4%nat))
      (point_at p (ordering 0%nat)) = B.

Definition maximizes_total_distance (p : five_points) : Prop :=
  forall q : five_points,
    on_unit_circle q ->
    total_distance q <= total_distance p.

Theorem putnam_1974_b1
    (p : five_points)
    (hp : on_unit_circle p) :
  maximizes_total_distance p <-> putnam_1974_b1_solution p.
Admitted.
