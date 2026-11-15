(* Statement-only formalization of PutnamBench artifact putnam_1966_b5:
   a finite planar point set in general position is the vertex set of a
   simple closed polygon. This file contains no proof. *)

From Stdlib Require Import Reals List.

Open Scope R_scope.

Definition point := (R * R)%type.
Definition point_set := point -> Prop.

Definition subset (A B : point_set) : Prop :=
  forall p : point, A p -> B p.

Definition has_cardinality (A : point_set) (n : nat) : Prop :=
  exists enumeration : list point,
    NoDup enumeration /\
    length enumeration = n /\
    forall p : point, In p enumeration <-> A p.

Definition affine_combination (t : R) (a b : point) : point :=
  ((1 - t) * fst a + t * fst b,
   (1 - t) * snd a + t * snd b).

Definition closed_segment (a b : point) : point_set :=
  fun p : point =>
    exists t : R,
      0 <= t <= 1 /\
      p = affine_combination t a b.

Definition collinear_points (a b c : point) : Prop :=
  (fst b - fst a) * (snd c - snd a) =
  (snd b - snd a) * (fst c - fst a).

Definition collinear (A : point_set) : Prop :=
  forall a b c : point,
    A a ->
    A b ->
    A c ->
    collinear_points a b c.

Theorem putnam_1966_b5
    (S : point_set)
    (n : nat)
    (hSfin : has_cardinality S n)
    (hcard : (3 <= n)%nat)
    (hS :
      forall s : point_set,
        subset s S ->
        has_cardinality s 3%nat ->
        ~ collinear s) :
  exists L : nat -> point,
    (forall p : point,
      S p ->
      exists! i : nat, (i < n)%nat /\ p = L i) /\
    (forall i j : nat,
      (i < n)%nat ->
      (j < n)%nat ->
      i <> j ->
      forall I : point,
        closed_segment
          (L i)
          (L (Nat.modulo (Nat.succ i) n))
          I /\
        closed_segment
          (L j)
          (L (Nat.modulo (Nat.succ j) n))
          I ->
        I = L i \/
        I = L (Nat.modulo (Nat.succ i) n) \/
        I = L j \/
        I = L (Nat.modulo (Nat.succ j) n)).
Admitted.
