(* Statement-only formalization of PutnamBench corpus artifact putnam_1998_b2:
   the minimum perimeter of a nondegenerate triangle with one vertex at a
   given point, one on the x-axis, and one on the line y = x. This file
   contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_1998_b2_distance
    (p q : (R * R)%type) : R :=
  sqrt ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2).

Definition putnam_1998_b2_perimeter
    (a b c x : R) : R :=
  putnam_1998_b2_distance (a, b) (c, 0) +
  putnam_1998_b2_distance (c, 0) (x, x) +
  putnam_1998_b2_distance (a, b) (x, x).

Definition putnam_1998_b2_nondegenerate
    (a b c x : R) : Prop :=
  putnam_1998_b2_distance (a, b) (c, 0) +
    putnam_1998_b2_distance (c, 0) (x, x) >
    putnam_1998_b2_distance (a, b) (x, x) /\
  putnam_1998_b2_distance (a, b) (c, 0) +
    putnam_1998_b2_distance (a, b) (x, x) >
    putnam_1998_b2_distance (c, 0) (x, x) /\
  putnam_1998_b2_distance (c, 0) (x, x) +
    putnam_1998_b2_distance (a, b) (x, x) >
    putnam_1998_b2_distance (a, b) (c, 0).

Definition putnam_1998_b2_candidate_perimeter
    (a b : R) (p : R) : Prop :=
  exists c x : R,
    p = putnam_1998_b2_perimeter a b c x /\
    putnam_1998_b2_nondegenerate a b c x.

Definition putnam_1998_b2_is_infimum
    (S : R -> Prop) (m : R) : Prop :=
  (forall p : R, S p -> m <= p) /\
  (forall lower : R,
      (forall p : R, S p -> lower <= p) ->
      lower <= m).

Definition putnam_1998_b2_solution (a b : R) : R :=
  sqrt (2 * a ^ 2 + 2 * b ^ 2).

Theorem putnam_1998_b2
    (a b : R)
    (hab : 0 < b /\ b < a) :
  putnam_1998_b2_is_infimum
    (putnam_1998_b2_candidate_perimeter a b)
    (putnam_1998_b2_solution a b).
Admitted.
