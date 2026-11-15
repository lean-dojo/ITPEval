(* Statement-only formalization of PutnamBench artifact putnam_1963_a6:
   the midpoint relation determined by three chords of an ellipse and their
   cross-line intersections. This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition point := (R * R)%type.
Definition point_set := point -> Prop.

Definition point_distance (a b : point) : R :=
  sqrt ((fst a - fst b) ^ 2 + (snd a - snd b) ^ 2).

Definition midpoint (a b : point) : point :=
  ((fst a + fst b) / 2, (snd a + snd b) / 2).

Definition affine_combination (t : R) (a b : point) : point :=
  ((1 - t) * fst a + t * fst b,
   (1 - t) * snd a + t * snd b).

Definition closed_segment (a b : point) : point_set :=
  fun p =>
    exists t : R,
      0 <= t <= 1 /\
      p = affine_combination t a b.

Definition same_set (A B : point_set) : Prop :=
  forall p : point, A p <-> B p.

Definition collinear_points (a b c : point) : Prop :=
  (fst b - fst a) * (snd c - snd a) =
  (snd b - snd a) * (fst c - fst a).

Theorem putnam_1963_a6 :
  forall
    (F1 F2 U V A B C D P Q : point)
    (r : R)
    (E : point_set)
    (M : point),
    (forall H : point,
      E H <->
      point_distance F1 H + point_distance F2 H = r) ->
    M = midpoint U V ->
    r > point_distance F1 F2 ->
    (E U /\ E V /\ U <> V) ->
    (E A /\ E B /\ A <> B) ->
    (E C /\ E D /\ C <> D) ->
    A <> C ->
    B <> D ->
    (~ same_set (closed_segment A B) (closed_segment U V) /\
     ~ same_set (closed_segment C D) (closed_segment U V) /\
     ~ same_set (closed_segment A B) (closed_segment C D)) ->
    (closed_segment A B M /\ closed_segment C D M) ->
    (collinear_points P A C /\ collinear_points P U V) ->
    (collinear_points Q B D /\ collinear_points Q U V) ->
    M = midpoint P Q.
Admitted.
