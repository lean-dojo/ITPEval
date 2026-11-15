(*
  Statement-only formalization of Thousand Theorems corpus artifact Q505798
  (thousand-theorems__rocq__Q505798), "Lagrange's theorem (group theory)":
  the natural cardinal of a subgroup of an arbitrary group divides the
  natural cardinal of the ambient group. This file contains no proof.
*)

From Stdlib Require Import Arith PeanoNat Logic.ClassicalEpsilon.

Set Universe Polymorphism.
Unset Implicit Arguments.

Record q505798_group (G : Type) : Type := {
  q505798_mul : G -> G -> G;
  q505798_one : G;
  q505798_inv : G -> G;
  q505798_mul_assoc :
    forall x y z : G,
      q505798_mul x (q505798_mul y z) =
      q505798_mul (q505798_mul x y) z;
  q505798_one_mul :
    forall x : G, q505798_mul q505798_one x = x;
  q505798_mul_one :
    forall x : G, q505798_mul x q505798_one = x;
  q505798_inv_mul :
    forall x : G,
      q505798_mul (q505798_inv x) x = q505798_one;
  q505798_mul_inv :
    forall x : G,
      q505798_mul x (q505798_inv x) = q505798_one
}.

Arguments q505798_mul {G} _ _ _.
Arguments q505798_one {G} _.
Arguments q505798_inv {G} _ _.

Record q505798_subgroup
    (G : Type)
    (grp : q505798_group G) : Type := {
  q505798_subgroup_mem : G -> Prop;
  q505798_subgroup_one :
    q505798_subgroup_mem (q505798_one grp);
  q505798_subgroup_mul :
    forall x y : G,
      q505798_subgroup_mem x ->
      q505798_subgroup_mem y ->
      q505798_subgroup_mem (q505798_mul grp x y);
  q505798_subgroup_inv :
    forall x : G,
      q505798_subgroup_mem x ->
      q505798_subgroup_mem (q505798_inv grp x)
}.

Arguments q505798_subgroup_mem {G grp} _ _.

Definition q505798_fin (n : nat) : Type :=
  { k : nat | k < n }.

Definition q505798_injective
    {A B : Type} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Definition q505798_has_cardinality
    {A : Type} (P : A -> Prop) (n : nat) : Prop :=
  exists enumerate : q505798_fin n -> A,
    q505798_injective enumerate /\
    (forall i : q505798_fin n, P (enumerate i)) /\
    forall x : A,
      P x ->
      exists i : q505798_fin n, enumerate i = x.

Definition q505798_nat_card
    {A : Type} (P : A -> Prop) : nat :=
  match excluded_middle_informative
          (exists n : nat, q505798_has_cardinality P n) with
  | left _ =>
      epsilon (inhabits 0)
        (fun n : nat => q505798_has_cardinality P n)
  | right _ => 0
  end.

Theorem Subgroup_card_subgroup_dvd_card :
  forall (G : Type)
         (grp : q505798_group G)
         (H : q505798_subgroup G grp),
    Nat.divide
      (q505798_nat_card (q505798_subgroup_mem H))
      (q505798_nat_card (fun _ : G => True)).
Admitted.
