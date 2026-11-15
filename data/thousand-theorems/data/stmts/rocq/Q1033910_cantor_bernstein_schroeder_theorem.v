(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1033910
  (thousand-theorems__rocq__Q1033910), "Cantor–Bernstein–Schroeder theorem":
  injections between arbitrary types in both directions imply the existence
  of a bijection. This file contains no proof.
*)

Set Universe Polymorphism.

Definition q1033910_injective
    {A B : Type} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Definition q1033910_surjective
    {A B : Type} (f : A -> B) : Prop :=
  forall y : B, exists x : A, f x = y.

Definition q1033910_bijective
    {A B : Type} (f : A -> B) : Prop :=
  q1033910_injective f /\ q1033910_surjective f.

Theorem Schroeder :
  forall (A B : Type) (f : A -> B) (g : B -> A),
    q1033910_injective f ->
    q1033910_injective g ->
    exists h : A -> B, q1033910_bijective h.
Admitted.
