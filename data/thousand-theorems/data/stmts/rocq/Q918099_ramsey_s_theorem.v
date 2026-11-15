(*
  Statement-only formalization of Thousand Theorems corpus artifact Q918099
  (thousand-theorems__rocq__Q918099), "Ramsey's theorem": every finite
  coloring of the r-element subsets of an infinite subset of the natural
  numbers has an infinite monochromatic subset. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Lists.List Sorting.Sorted.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q918099_finset (A : Type) : Type := {
  q918099_elements : list A;
  q918099_elements_nodup : NoDup q918099_elements
}.

Arguments q918099_elements {A} _.

Definition q918099_mem
    {A : Type} (x : A) (s : q918099_finset A) : Prop :=
  In x (q918099_elements s).

Definition q918099_subset
    (M2 M1 : nat -> Prop) : Prop :=
  forall x : nat, M2 x -> M1 x.

Definition q918099_infinite
    (M : nat -> Prop) : Prop :=
  ~ exists enumeration : list nat,
      forall x : nat, M x <-> In x enumeration.

Definition q918099_edge
    (r : nat) (M : nat -> Prop) (edge : list nat) : Prop :=
  StronglySorted Nat.lt edge /\
  length edge = r /\
  forall x : nat, In x edge -> M x.

Theorem ramsey_r :
  forall (A : Type)
         (K : q918099_finset A)
         (r : nat)
         (M1 : nat -> Prop),
    q918099_infinite M1 ->
    forall c : list nat -> A,
      (forall edge : list nat,
        q918099_edge r M1 edge ->
        q918099_mem (c edge) K) ->
      exists M2 : nat -> Prop,
        q918099_subset M2 M1 /\
        q918099_infinite M2 /\
        exists color : A,
          q918099_mem color K /\
          forall edge : list nat,
            q918099_edge r M2 edge ->
            c edge = color.
Admitted.
