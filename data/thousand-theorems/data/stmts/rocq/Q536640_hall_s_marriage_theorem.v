(*
  Statement-only formalization of Thousand Theorems corpus artifact Q536640
  (thousand-theorems__rocq__Q536640), "Hall's marriage theorem": an indexed
  family of finite sets has an injective system of representatives if and
  only if every finite subfamily has a union at least as large as the
  subfamily. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Lists.List.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q536640_finset (X : Type) : Type := {
  q536640_elements : list X;
  q536640_elements_nodup : NoDup q536640_elements
}.

Arguments q536640_elements {X} _.

Definition q536640_mem
    {X : Type} (x : X) (s : q536640_finset X) : Prop :=
  In x (q536640_elements s).

Definition q536640_biunion_elements
    {I A : Type}
    (t : I -> q536640_finset A)
    (s : q536640_finset I) : list A :=
  flat_map
    (fun i : I => q536640_elements (t i))
    (q536640_elements s).

Definition q536640_biunion_card
    {I A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (t : I -> q536640_finset A)
    (s : q536640_finset I) : nat :=
  length (nodup eq_dec (q536640_biunion_elements t s)).

Definition q536640_injective
    {I A : Type} (f : I -> A) : Prop :=
  forall x y : I, f x = f y -> x = y.

Module Finset.

Theorem all_card_le_biUnion_card_iff_exists_injective :
  forall (I A : Type)
         (eq_dec : forall x y : A, {x = y} + {x <> y})
         (t : I -> q536640_finset A),
    (forall s : q536640_finset I,
      (length (q536640_elements s) <=
       q536640_biunion_card eq_dec t s)%nat) <->
    exists f : I -> A,
      q536640_injective f /\
      forall x : I, q536640_mem (f x) (t x).
Admitted.

End Finset.
