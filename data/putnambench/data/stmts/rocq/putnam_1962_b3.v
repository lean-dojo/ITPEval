(* Statement-only formalization of PutnamBench artifact putnam_1962_b3:
   a convex subset of the Euclidean plane satisfying the stated topological
   condition and omitting a point on every ray from the origin is bounded.
   This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition point := (R * R)%type.
Definition point_set := point -> Prop.

Definition origin : point := (0, 0).

Definition point_scale (k : R) (p : point) : point :=
  (k * fst p, k * snd p).

Definition affine_combination
    (t : R) (p q : point) : point :=
  ((1 - t) * fst p + t * fst q,
   (1 - t) * snd p + t * snd q).

Definition squared_distance (p q : point) : R :=
  (fst p - fst q) * (fst p - fst q) +
  (snd p - snd q) * (snd p - snd q).

Definition convex (S : point_set) : Prop :=
  forall (p q : point) (t : R),
    S p ->
    S q ->
    0 <= t <= 1 ->
    S (affine_combination t p q).

Definition origin_is_interior (S : point_set) : Prop :=
  exists epsilon : R,
    0 < epsilon /\
    forall p : point,
      squared_distance p origin < epsilon * epsilon ->
      S p.

Definition converges_to (u : nat -> point) (p : point) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        squared_distance (u n) p < epsilon * epsilon.

Definition closed (S : point_set) : Prop :=
  forall (u : nat -> point) (p : point),
    (forall n : nat, S (u n)) ->
    converges_to u p ->
    S p.

Definition same_ray (p q : point) : Prop :=
  exists k : R,
    0 < k /\
    q = point_scale k p.

Definition bounded (S : point_set) : Prop :=
  exists radius : R,
    0 <= radius /\
    forall p : point,
      S p ->
      squared_distance p origin <= radius * radius.

Theorem putnam_1962_b3 :
  forall S : point_set,
    (convex S /\ S origin) ->
    (origin_is_interior S \/ closed S) ->
    (forall P : point,
      P <> origin ->
      exists Q : point,
        same_ray P Q /\ ~ S Q) ->
    bounded S.
Admitted.
