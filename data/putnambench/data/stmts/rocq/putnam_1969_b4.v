(* Statement-only formalization of PutnamBench artifact putnam_1969_b4:
   a continuous plane curve of total variation one is covered by a closed
   rectangle of area one quarter. This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition point := (R * R)%type.
Definition point_set := point -> Prop.

Definition point_subtract (p q : point) : point :=
  (fst p - fst q, snd p - snd q).

Definition point_dot (p q : point) : R :=
  fst p * fst q + snd p * snd q.

Definition point_determinant (p q : point) : R :=
  fst p * snd q - snd p * fst q.

Definition point_distance (p q : point) : R :=
  sqrt ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2).

Definition affine_combination (t : R) (p q : point) : point :=
  ((1 - t) * fst p + t * fst q,
   (1 - t) * snd p + t * snd q).

Definition subset (A B : point_set) : Prop :=
  forall p : point, A p -> B p.

Definition convex (S : point_set) : Prop :=
  forall (p q : point) (t : R),
    S p ->
    S q ->
    0 <= t <= 1 ->
    S (affine_combination t p q).

Definition convex_hull (S : point_set) : point_set :=
  fun p : point =>
    forall C : point_set,
      convex C ->
      subset S C ->
      C p.

Definition four_points (a b c d : point) : point_set :=
  fun p : point => p = a \/ p = b \/ p = c \/ p = d.

Definition curve_continuous_on_unit_interval
    (Gamma : R -> point) : Prop :=
  forall t : R,
    0 <= t <= 1 ->
    forall epsilon : R,
      0 < epsilon ->
      exists delta : R,
        0 < delta /\
        forall u : R,
          0 <= u <= 1 ->
          Rabs (u - t) < delta ->
          point_distance (Gamma u) (Gamma t) < epsilon.

Fixpoint chain_sum
    (Gamma : R -> point) (parameters : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S k =>
      chain_sum Gamma parameters k +
      point_distance (Gamma (parameters k)) (Gamma (parameters (S k)))
  end.

Definition valid_unit_interval_chain
    (parameters : nat -> R) (n : nat) : Prop :=
  (forall i : nat,
      (i <= n)%nat ->
      0 <= parameters i <= 1) /\
  (forall i : nat,
      (i < n)%nat ->
      parameters i <= parameters (S i)).

Definition curve_total_variation_one
    (Gamma : R -> point) : Prop :=
  (forall (n : nat) (parameters : nat -> R),
      valid_unit_interval_chain parameters n ->
      chain_sum Gamma parameters n <= 1) /\
  (forall lower : R,
      lower < 1 ->
      exists (n : nat) (parameters : nat -> R),
        valid_unit_interval_chain parameters n /\
        lower < chain_sum Gamma parameters n).

Definition oriented_right_angle (a b c : point) : Prop :=
  let ba := point_subtract a b in
  let bc := point_subtract c b in
  point_dot ba bc = 0 /\ 0 < point_determinant ba bc.

Theorem putnam_1969_b4
    (Gamma : R -> point)
    (Gamma_continuous : curve_continuous_on_unit_interval Gamma)
    (Gamma_length : curve_total_variation_one Gamma) :
  exists a b c d : point,
    (forall t : R,
      0 <= t <= 1 ->
      convex_hull (four_points a b c d) (Gamma t)) /\
    point_distance a b * point_distance b c = 1 / 4 /\
    oriented_right_angle a b c /\
    oriented_right_angle b c d /\
    oriented_right_angle c d a /\
    oriented_right_angle d a b.
Admitted.
