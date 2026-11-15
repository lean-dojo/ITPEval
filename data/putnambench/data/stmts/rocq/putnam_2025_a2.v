(* Statement-only formalization of PutnamBench putnam_2025_a2: the sharp
   real constants bounding sine by x(PI-x) on [0, PI]; this file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_2025_a2_solution : (R * R)%type :=
  (1 / PI, 4 / PI ^ 2).

Definition putnam_2025_a2_lower_bound (a : R) : Prop :=
  forall x : R,
    0 <= x /\ x <= PI ->
    a * x * (PI - x) <= sin x.

Definition putnam_2025_a2_upper_bound (b : R) : Prop :=
  forall x : R,
    0 <= x /\ x <= PI ->
    sin x <= b * x * (PI - x).

Definition putnam_2025_a2_is_greatest
    (property : R -> Prop) (greatest : R) : Prop :=
  property greatest /\
  forall candidate : R, property candidate -> candidate <= greatest.

Definition putnam_2025_a2_is_least
    (property : R -> Prop) (least : R) : Prop :=
  property least /\
  forall candidate : R, property candidate -> least <= candidate.

Theorem putnam_2025_a2 (a b : R) :
  (a, b) = putnam_2025_a2_solution <->
  putnam_2025_a2_is_greatest putnam_2025_a2_lower_bound a /\
  putnam_2025_a2_is_least putnam_2025_a2_upper_bound b.
Admitted.
