(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2004_b6:
  unbounded consecutive gaps in the increasing positive-difference set of a
  nonempty set of positive integers force its counting density to tend to zero.
  This file contains no proof.
*)

From Stdlib Require Import Reals List Arith.PeanoNat.

Open Scope R_scope.

Definition putnam_2004_b6_has_cardinality
    (P : nat -> Prop) (n : nat) : Prop :=
  exists enumeration : list nat,
    NoDup enumeration /\
    length enumeration = n /\
    forall a : nat, In a enumeration <-> P a.

Definition putnam_2004_b6_tends_to_zero_at_pos_infinity
    (f : R -> R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists cutoff : R,
      forall x : R,
        cutoff <= x ->
        Rabs (f x - 0) < epsilon.

Theorem putnam_2004_b6
    (A B : nat -> Prop)
    (N : R -> nat)
    (b : nat -> nat)
    (Anempty : exists a : nat, A a)
    (Apos : forall a : nat, A a -> (0 < a)%nat)
    (hN :
      forall x : R,
        putnam_2004_b6_has_cardinality
          (fun a : nat => A a /\ INR a <= x)
          (N x))
    (hB :
      forall d : nat,
        B d <->
        (0 < d)%nat /\
        exists a a' : nat,
          A a /\ A a' /\ d = (a - a')%nat)
    (hbB :
      forall d : nat,
        B d <-> exists i : nat, b i = d)
    (hbasc :
      forall i : nat, (b i < b (S i))%nat) :
  (forall r : nat,
      exists i : nat, (r <= b (S i) - b i)%nat) ->
  putnam_2004_b6_tends_to_zero_at_pos_infinity
    (fun x : R => INR (N x) / x).
Admitted.
