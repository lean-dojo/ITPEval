(* Statement-only formalization of PutnamBench artifact putnam_1998_a5:
   a finite cover of a planar set by positive-radius open discs has a
   pairwise disjoint subcollection whose tripled discs still cover the set.
   This file contains no proof. *)

From Stdlib Require Import Reals Arith.PeanoNat.

Open Scope R_scope.

Definition putnam_1998_a5_point := (R * R)%type.
Definition putnam_1998_a5_point_set :=
  putnam_1998_a5_point -> Prop.

Definition putnam_1998_a5_squared_distance
    (p q : putnam_1998_a5_point) : R :=
  (fst p - fst q) ^ 2 + (snd p - snd q) ^ 2.

Definition putnam_1998_a5_open_disc
    (center : putnam_1998_a5_point)
    (radius : R)
    (p : putnam_1998_a5_point) : Prop :=
  putnam_1998_a5_squared_distance p center < radius ^ 2.

Theorem putnam_1998_a5
    (k : nat)
    (c : nat -> putnam_1998_a5_point)
    (r : nat -> R)
    (E : putnam_1998_a5_point_set)
    (hr : forall i : nat, (i < k)%nat -> 0 < r i)
    (hE :
      forall p : putnam_1998_a5_point,
        E p ->
        exists i : nat,
          (i < k)%nat /\
          putnam_1998_a5_open_disc (c i) (r i) p) :
  exists (n : nat) (t : nat -> nat),
    (n <= k)%nat /\
    (forall i : nat, (i < n)%nat -> (t i < k)%nat) /\
    (forall i j : nat,
      (i < n)%nat ->
      (j < n)%nat ->
      i <> j ->
      forall p : putnam_1998_a5_point,
        ~ (putnam_1998_a5_open_disc (c (t i)) (r (t i)) p /\
           putnam_1998_a5_open_disc (c (t j)) (r (t j)) p)) /\
    forall p : putnam_1998_a5_point,
      E p ->
      exists i : nat,
        (i < n)%nat /\
        putnam_1998_a5_open_disc (c (t i)) (3 * r (t i)) p.
Admitted.
