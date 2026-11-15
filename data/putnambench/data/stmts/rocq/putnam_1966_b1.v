(* Statement-only formalization of PutnamBench artifact putnam_1966_b1:
   a convex polygon contained in the unit square has sum of squared side
   lengths at most four. This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition point := (R * R)%type.
Definition point_set := point -> Prop.

Definition point_distance (a b : point) : R :=
  sqrt ((fst a - fst b) ^ 2 + (snd a - snd b) ^ 2).

Definition affine_combination (t : R) (a b : point) : point :=
  ((1 - t) * fst a + t * fst b,
   (1 - t) * snd a + t * snd b).

Definition closed_segment (a b : point) : point_set :=
  fun p : point =>
    exists t : R,
      0 <= t <= 1 /\
      p = affine_combination t a b.

Definition subset (A B : point_set) : Prop :=
  forall p : point, A p -> B p.

Definition convex (A : point_set) : Prop :=
  forall (a b : point) (t : R),
    A a ->
    A b ->
    0 <= t <= 1 ->
    A (affine_combination t a b).

Definition convex_hull (A : point_set) : point_set :=
  fun p : point =>
    forall C : point_set,
      convex C ->
      subset A C ->
      C p.

Definition interior (A : point_set) : point_set :=
  fun p : point =>
    exists epsilon : R,
      0 < epsilon /\
      forall q : point,
        point_distance q p < epsilon ->
        A q.

Definition collinear_points (a b c : point) : Prop :=
  (fst b - fst a) * (snd c - snd a) =
  (snd b - snd a) * (fst c - fst a).

Definition polygon_vertices
    (n : nat) (L : nat -> point) : point_set :=
  fun p : point =>
    exists i : nat,
      (i < n)%nat /\
      L i = p.

Fixpoint sum_first_n (f : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S k => sum_first_n f k + f k
  end.

Theorem putnam_1966_b1
    (n : nat)
    (hn : (3 <= n)%nat)
    (L : nat -> point)
    (hsq :
      forall i : nat,
        (i < n)%nat ->
        0 <= fst (L i) <= 1 /\
        0 <= snd (L i) <= 1)
    (hnoncol :
      forall i j k : nat,
        (i < n)%nat ->
        (j < n)%nat ->
        (k < n)%nat ->
        i <> j ->
        j <> k ->
        k <> i ->
        ~ collinear_points (L i) (L j) (L k))
    (hconvex :
      forall i : nat,
        (i < n)%nat ->
        forall p : point,
          closed_segment
            (L i)
            (L (Nat.modulo (S i) n))
            p ->
          ~ interior (convex_hull (polygon_vertices n L)) p) :
  sum_first_n
    (fun i : nat =>
      point_distance (L i) (L (Nat.modulo (S i) n)) ^ 2)
    n <= 4.
Admitted.
