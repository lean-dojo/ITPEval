(* Statement-only formalization of PutnamBench corpus artifact putnam_1987_b6:
   parity of the intersection of a sign-representative subset of the finite
   field of p^2 elements with its doubled image. This file contains no proof. *)

From Stdlib Require Import Field Lists.List Arith.PeanoNat.

Record putnam_1987_b6_finite_field : Type := {
  ff_carrier : Type;
  ff_zero : ff_carrier;
  ff_one : ff_carrier;
  ff_add : ff_carrier -> ff_carrier -> ff_carrier;
  ff_mul : ff_carrier -> ff_carrier -> ff_carrier;
  ff_sub : ff_carrier -> ff_carrier -> ff_carrier;
  ff_opp : ff_carrier -> ff_carrier;
  ff_div : ff_carrier -> ff_carrier -> ff_carrier;
  ff_inv : ff_carrier -> ff_carrier;
  ff_field_theory :
    field_theory
      ff_zero ff_one ff_add ff_mul ff_sub ff_opp ff_div ff_inv eq;
  ff_elements : list ff_carrier;
  ff_elements_nodup : NoDup ff_elements;
  ff_elements_complete : forall x : ff_carrier, In x ff_elements
}.

Arguments ff_zero {_}.
Arguments ff_add {_} _ _.
Arguments ff_opp {_} _.

Definition putnam_1987_b6_prime (p : nat) : Prop :=
  (2 <= p)%nat /\
  forall d : nat, Nat.divide d p -> d = 1%nat \/ d = p.

Definition putnam_1987_b6_has_cardinality
    {A : Type} (S : A -> Prop) (n : nat) : Prop :=
  exists xs : list A,
    NoDup xs /\
    (forall x : A, In x xs <-> S x) /\
    length xs = n.

Definition putnam_1987_b6_has_even_cardinality
    {A : Type} (S : A -> Prop) : Prop :=
  exists xs : list A,
    NoDup xs /\
    (forall x : A, In x xs <-> S x) /\
    Nat.Even (length xs).

Theorem putnam_1987_b6
    (p : nat)
    (F : putnam_1987_b6_finite_field)
    (S : ff_carrier F -> Prop)
    (hp : Nat.Odd p /\ putnam_1987_b6_prime p)
    (Fcard : length (ff_elements F) = Nat.pow p 2)
    (Snz : forall x : ff_carrier F, S x -> x <> ff_zero)
    (Scard :
      putnam_1987_b6_has_cardinality
        S (Nat.div (Nat.pow p 2 - 1) 2))
    (hS : forall a : ff_carrier F,
      a <> ff_zero ->
      (S a /\ ~ S (ff_opp a)) \/ (~ S a /\ S (ff_opp a))) :
  putnam_1987_b6_has_even_cardinality
    (fun x : ff_carrier F =>
      S x /\
      exists a : ff_carrier F, S a /\ x = ff_add a a).
Admitted.
