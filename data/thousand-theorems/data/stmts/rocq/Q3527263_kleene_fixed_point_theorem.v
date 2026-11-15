(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527263
  (thousand-theorems__rocq__Q3527263), "Kleene fixed-point theorem": on a
  complete lattice, the least fixed point of an omega-Scott-continuous
  monotone endomap is the supremum of its finite iterates from bottom.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q3527263_complete_lattice (A : Type) : Type := {
  q3527263_le : A -> A -> Prop;
  q3527263_le_refl :
    forall x : A, q3527263_le x x;
  q3527263_le_trans :
    forall x y z : A,
      q3527263_le x y ->
      q3527263_le y z ->
      q3527263_le x z;
  q3527263_le_antisym :
    forall x y : A,
      q3527263_le x y ->
      q3527263_le y x ->
      x = y;
  q3527263_bottom : A;
  q3527263_bottom_le :
    forall x : A, q3527263_le q3527263_bottom x;
  q3527263_supremum : (A -> Prop) -> A;
  q3527263_le_supremum :
    forall (S : A -> Prop) (x : A),
      S x ->
      q3527263_le x (q3527263_supremum S);
  q3527263_supremum_le :
    forall (S : A -> Prop) (upper : A),
      (forall x : A, S x -> q3527263_le x upper) ->
      q3527263_le (q3527263_supremum S) upper;
  q3527263_infimum : (A -> Prop) -> A;
  q3527263_infimum_le :
    forall (S : A -> Prop) (x : A),
      S x ->
      q3527263_le (q3527263_infimum S) x;
  q3527263_le_infimum :
    forall (S : A -> Prop) (lower : A),
      (forall x : A, S x -> q3527263_le lower x) ->
      q3527263_le lower (q3527263_infimum S)
}.

Arguments q3527263_le {A} _ _ _.
Arguments q3527263_bottom {A} _.
Arguments q3527263_supremum {A} _ _.
Arguments q3527263_infimum {A} _ _.

Record q3527263_order_hom
    (A : Type) (L : q3527263_complete_lattice A) : Type := {
  q3527263_hom_fun : A -> A;
  q3527263_hom_monotone :
    forall x y : A,
      q3527263_le L x y ->
      q3527263_le L (q3527263_hom_fun x) (q3527263_hom_fun y)
}.

Arguments q3527263_order_hom A L : clear implicits.
Arguments q3527263_hom_fun {A L} _ _.

Definition q3527263_range {A : Type}
    (u : nat -> A) : A -> Prop :=
  fun x => exists n : nat, x = u n.

Definition q3527263_increasing {A : Type}
    (L : q3527263_complete_lattice A)
    (u : nat -> A) : Prop :=
  forall n m : nat,
    Nat.le n m ->
    q3527263_le L (u n) (u m).

Definition q3527263_omega_scott_continuous
    {A : Type}
    (L : q3527263_complete_lattice A)
    (f : q3527263_order_hom A L) : Prop :=
  forall u : nat -> A,
    q3527263_increasing L u ->
    q3527263_hom_fun f
      (q3527263_supremum L (q3527263_range u)) =
    q3527263_supremum L
      (q3527263_range (fun n : nat => q3527263_hom_fun f (u n))).

Definition q3527263_lfp
    {A : Type}
    (L : q3527263_complete_lattice A)
    (f : q3527263_order_hom A L) : A :=
  q3527263_infimum L
    (fun x : A => q3527263_le L (q3527263_hom_fun f x) x).

Fixpoint q3527263_iterate
    {A : Type}
    (f : A -> A) (n : nat) (x : A) : A :=
  match n with
  | O => x
  | S k => f (q3527263_iterate f k x)
  end.

Module fixedPoints.

Theorem lfp_eq_sSup_iterate :
  forall (A : Type)
         (L : q3527263_complete_lattice A)
         (f : q3527263_order_hom A L),
    @q3527263_omega_scott_continuous A L f ->
    @q3527263_lfp A L f =
    q3527263_supremum L
      (q3527263_range
        (fun n : nat =>
          q3527263_iterate
            (q3527263_hom_fun f) n (q3527263_bottom L))).
Admitted.

End fixedPoints.
