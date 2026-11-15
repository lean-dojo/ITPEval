(* Statement-only formalization of PutnamBench artifact putnam_1975_b4:
   nonexistence of a topologically closed subset of the real unit circle
   containing exactly one point from each antipodal pair. This file contains
   no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_1975_b4_point : Type := (R * R)%type.

Definition putnam_1975_b4_set : Type :=
  putnam_1975_b4_point -> Prop.

Definition putnam_1975_b4_unit_circle
    (p : putnam_1975_b4_point) : Prop :=
  (fst p) ^ 2 + (snd p) ^ 2 = 1.

(* Closedness in the usual product topology on R x R. *)
Definition putnam_1975_b4_closed
    (B : putnam_1975_b4_set) : Prop :=
  forall p : putnam_1975_b4_point,
    ~ B p ->
    exists epsilon : R,
      epsilon > 0 /\
      forall q : putnam_1975_b4_point,
        Rabs (fst q - fst p) < epsilon ->
        Rabs (snd q - snd p) < epsilon ->
        ~ B q.

Definition putnam_1975_b4_solution : Prop := False.

Theorem putnam_1975_b4
    (P : putnam_1975_b4_set)
    (hP : P = putnam_1975_b4_unit_circle) :
  (exists B : putnam_1975_b4_set,
      (forall p : putnam_1975_b4_point, B p -> P p) /\
      putnam_1975_b4_closed B /\
      forall x y : R,
        P (x, y) ->
        (B (x, y) /\ ~ B (-x, -y)) \/
        (~ B (x, y) /\ B (-x, -y))) <->
  putnam_1975_b4_solution.
Admitted.
