(* Statement-only formalization of PutnamBench corpus artifact putnam_2013_a5:
   area-definite real coefficients for triangles in the Euclidean plane remain
   area definite for triangles in Euclidean three-space. This file contains no
   proof. *)

From Stdlib Require Import Reals Arith.PeanoNat.

Open Scope R_scope.

Definition putnam_2013_a5_point2 : Type := (R * R)%type.
Definition putnam_2013_a5_point3 : Type := (R * (R * R))%type.

Definition putnam_2013_a5_area2
    (a b c : putnam_2013_a5_point2) : R :=
  Rabs
    ((fst b - fst a) * (snd c - snd a) -
     (snd b - snd a) * (fst c - fst a)) / 2.

Definition putnam_2013_a5_cross_x
    (a b c : putnam_2013_a5_point3) : R :=
  (fst (snd b) - fst (snd a)) * (snd (snd c) - snd (snd a)) -
  (snd (snd b) - snd (snd a)) * (fst (snd c) - fst (snd a)).

Definition putnam_2013_a5_cross_y
    (a b c : putnam_2013_a5_point3) : R :=
  (snd (snd b) - snd (snd a)) * (fst c - fst a) -
  (fst b - fst a) * (snd (snd c) - snd (snd a)).

Definition putnam_2013_a5_cross_z
    (a b c : putnam_2013_a5_point3) : R :=
  (fst b - fst a) * (fst (snd c) - fst (snd a)) -
  (fst (snd b) - fst (snd a)) * (fst c - fst a).

Definition putnam_2013_a5_area3
    (a b c : putnam_2013_a5_point3) : R :=
  sqrt
    (putnam_2013_a5_cross_x a b c ^ 2 +
     putnam_2013_a5_cross_y a b c ^ 2 +
     putnam_2013_a5_cross_z a b c ^ 2) / 2.

Fixpoint putnam_2013_a5_sum_first
    (n : nat) (f : nat -> R) : R :=
  match n with
  | O => 0
  | S k => putnam_2013_a5_sum_first k f + f k
  end.

Definition putnam_2013_a5_weighted_sum2
    (m : nat)
    (coefficients : nat -> nat -> nat -> R)
    (points : nat -> putnam_2013_a5_point2) : R :=
  putnam_2013_a5_sum_first m
    (fun i =>
      putnam_2013_a5_sum_first m
        (fun j =>
          putnam_2013_a5_sum_first m
            (fun k =>
              if andb (Nat.ltb i j) (Nat.ltb j k)
              then coefficients i j k *
                putnam_2013_a5_area2 (points i) (points j) (points k)
              else 0))).

Definition putnam_2013_a5_weighted_sum3
    (m : nat)
    (coefficients : nat -> nat -> nat -> R)
    (points : nat -> putnam_2013_a5_point3) : R :=
  putnam_2013_a5_sum_first m
    (fun i =>
      putnam_2013_a5_sum_first m
        (fun j =>
          putnam_2013_a5_sum_first m
            (fun k =>
              if andb (Nat.ltb i j) (Nat.ltb j k)
              then coefficients i j k *
                putnam_2013_a5_area3 (points i) (points j) (points k)
              else 0))).

Definition putnam_2013_a5_area_definite2
    (m : nat) (coefficients : nat -> nat -> nat -> R) : Prop :=
  forall points : nat -> putnam_2013_a5_point2,
    0 <= putnam_2013_a5_weighted_sum2 m coefficients points.

Definition putnam_2013_a5_area_definite3
    (m : nat) (coefficients : nat -> nat -> nat -> R) : Prop :=
  forall points : nat -> putnam_2013_a5_point3,
    0 <= putnam_2013_a5_weighted_sum3 m coefficients points.

Theorem putnam_2013_a5 :
  forall (m : nat) (coefficients : nat -> nat -> nat -> R),
    (3 <= m)%nat ->
    putnam_2013_a5_area_definite2 m coefficients ->
    putnam_2013_a5_area_definite3 m coefficients.
Admitted.
