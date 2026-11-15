(* Statement-only formalization of PutnamBench artifact putnam_1966_a2:
   an inequality relating the side lengths, semiperimeter, and inradius of a
   nondegenerate planar triangle under the stated incenter and enclosed-disk
   conditions. This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition point := (R * R)%type.
Definition point_set := point -> Prop.

Definition point_distance (a b : point) : R :=
  sqrt ((fst a - fst b) ^ 2 + (snd a - snd b) ^ 2).

Definition collinear_points (a b c : point) : Prop :=
  (fst b - fst a) * (snd c - snd a) =
  (snd b - snd a) * (fst c - fst a).

Definition tripleton (a b c : point) : point_set :=
  fun x : point => x = a \/ x = b \/ x = c.

Definition subset (A B : point_set) : Prop :=
  forall x : point, A x -> B x.

Definition affine_combination
    (lambda : R) (a b : point) : point :=
  ((1 - lambda) * fst a + lambda * fst b,
   (1 - lambda) * snd a + lambda * snd b).

Definition convex (A : point_set) : Prop :=
  forall (a b : point) (lambda : R),
    A a ->
    A b ->
    0 <= lambda <= 1 ->
    A (affine_combination lambda a b).

Definition convex_hull (A : point_set) : point_set :=
  fun x : point =>
    forall C : point_set,
      convex C ->
      subset A C ->
      C x.

Theorem putnam_1966_a2
    (r : R)
    (A B C : point)
    (hABC : ~ collinear_points A B C)
    (a b c p : R)
    (ha : a = point_distance B C)
    (hb : b = point_distance C A)
    (hc : c = point_distance A B)
    (hp : p =
      (point_distance B C + point_distance C A + point_distance A B) / 2)
    (hr :
      exists I : point,
        (exists! P : point,
          point_distance I P = r /\ collinear_points P B C) /\
        (exists! Q : point,
          point_distance I Q = r /\ collinear_points Q C A) /\
        (exists! R0 : point,
          point_distance I R0 = r /\ collinear_points R0 A B) /\
        (forall Z : point,
          point_distance I Z <= r ->
          convex_hull (tripleton A B C) Z)) :
  1 / (p - a) ^ 2 + 1 / (p - b) ^ 2 + 1 / (p - c) ^ 2
    >= 1 / r ^ 2.
Admitted.
