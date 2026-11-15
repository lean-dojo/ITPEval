(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1139041
  (thousand-theorems__rocq__Q1139041), "Cauchy's theorem (group theory)":
  every prime dividing the cardinality of a finite group is the order of
  some group element. This file contains no proof.
*)

From Stdlib Require Import List Arith PeanoNat.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q1139041_group (G : Type) : Type := {
  q1139041_mul : G -> G -> G;
  q1139041_one : G;
  q1139041_inv : G -> G;
  q1139041_mul_assoc :
    forall x y z : G,
      q1139041_mul x (q1139041_mul y z) =
      q1139041_mul (q1139041_mul x y) z;
  q1139041_one_mul :
    forall x : G, q1139041_mul q1139041_one x = x;
  q1139041_mul_one :
    forall x : G, q1139041_mul x q1139041_one = x;
  q1139041_inv_mul :
    forall x : G,
      q1139041_mul (q1139041_inv x) x = q1139041_one;
  q1139041_mul_inv :
    forall x : G,
      q1139041_mul x (q1139041_inv x) = q1139041_one
}.

Arguments q1139041_mul {G} _ _ _.
Arguments q1139041_one {G} _.

Record q1139041_finite_type (G : Type) : Type := {
  q1139041_enum : list G;
  q1139041_enum_nodup : NoDup q1139041_enum;
  q1139041_enum_complete :
    forall x : G, In x q1139041_enum
}.

Arguments q1139041_enum {G} _.

Definition q1139041_finite_card
    {G : Type} (F : q1139041_finite_type G) : nat :=
  length (q1139041_enum F).

Fixpoint q1139041_pow
    {G : Type}
    (grp : q1139041_group G)
    (x : G)
    (n : nat) : G :=
  match n with
  | 0 => q1139041_one grp
  | S k => q1139041_mul grp x (q1139041_pow grp x k)
  end.

Definition q1139041_prime (p : nat) : Prop :=
  (1 < p)%nat /\
  forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition q1139041_has_order
    {G : Type}
    (grp : q1139041_group G)
    (x : G)
    (n : nat) : Prop :=
  (0 < n)%nat /\
  q1139041_pow grp x n = q1139041_one grp /\
  forall k : nat,
    (0 < k < n)%nat ->
    q1139041_pow grp x k <> q1139041_one grp.

Theorem exists_prime_orderOf_dvd_card :
  forall (G : Type)
         (grp : q1139041_group G)
         (F : q1139041_finite_type G)
         (p : nat),
    q1139041_prime p ->
    Nat.divide p (q1139041_finite_card F) ->
    exists x : G, q1139041_has_order grp x p.
Admitted.
