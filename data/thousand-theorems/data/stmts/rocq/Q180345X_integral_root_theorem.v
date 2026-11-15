(*
  Statement-only formalization of Thousand Theorems corpus artifact Q180345X
  (thousand-theorems__rocq__Q180345X), "Integral root theorem": every root in
  the fraction field of a unique factorization domain of a monic polynomial
  over that domain lies in the image of the domain. This file contains no proof.
*)

From Stdlib Require Import List Arith.

Import ListNotations.
Set Universe Polymorphism.
Set Implicit Arguments.

Record q180345x_commutative_ring (A : Type) : Type := {
  q180345x_zero : A;
  q180345x_one : A;
  q180345x_add : A -> A -> A;
  q180345x_mul : A -> A -> A;
  q180345x_neg : A -> A;
  q180345x_add_comm :
    forall x y : A,
      q180345x_add x y = q180345x_add y x;
  q180345x_add_assoc :
    forall x y z : A,
      q180345x_add (q180345x_add x y) z =
      q180345x_add x (q180345x_add y z);
  q180345x_add_zero :
    forall x : A,
      q180345x_add x q180345x_zero = x;
  q180345x_add_neg :
    forall x : A,
      q180345x_add x (q180345x_neg x) = q180345x_zero;
  q180345x_mul_comm :
    forall x y : A,
      q180345x_mul x y = q180345x_mul y x;
  q180345x_mul_assoc :
    forall x y z : A,
      q180345x_mul (q180345x_mul x y) z =
      q180345x_mul x (q180345x_mul y z);
  q180345x_mul_one :
    forall x : A,
      q180345x_mul x q180345x_one = x;
  q180345x_mul_add :
    forall x y z : A,
      q180345x_mul x (q180345x_add y z) =
      q180345x_add
        (q180345x_mul x y) (q180345x_mul x z)
}.

Arguments q180345x_zero {A} _.
Arguments q180345x_one {A} _.
Arguments q180345x_add {A} _ _ _.
Arguments q180345x_mul {A} _ _ _.
Arguments q180345x_neg {A} _ _.

Record q180345x_integral_domain (A : Type) : Type := {
  q180345x_domain_ring : q180345x_commutative_ring A;
  q180345x_one_ne_zero :
    q180345x_one q180345x_domain_ring <>
    q180345x_zero q180345x_domain_ring;
  q180345x_no_zero_divisors :
    forall x y : A,
      q180345x_mul q180345x_domain_ring x y =
      q180345x_zero q180345x_domain_ring ->
      x = q180345x_zero q180345x_domain_ring \/
      y = q180345x_zero q180345x_domain_ring
}.

Arguments q180345x_domain_ring {A} _.

Record q180345x_field (K : Type) : Type := {
  q180345x_field_ring : q180345x_commutative_ring K;
  q180345x_inv : K -> K;
  q180345x_field_one_ne_zero :
    q180345x_one q180345x_field_ring <>
    q180345x_zero q180345x_field_ring;
  q180345x_mul_inv :
    forall x : K,
      x <> q180345x_zero q180345x_field_ring ->
      q180345x_mul q180345x_field_ring x (q180345x_inv x) =
      q180345x_one q180345x_field_ring
}.

Arguments q180345x_field_ring {K} _.

Record q180345x_ring_hom
    {A K : Type}
    (RA : q180345x_commutative_ring A)
    (RK : q180345x_commutative_ring K) : Type := {
  q180345x_map : A -> K;
  q180345x_map_zero :
    q180345x_map (q180345x_zero RA) = q180345x_zero RK;
  q180345x_map_one :
    q180345x_map (q180345x_one RA) = q180345x_one RK;
  q180345x_map_add :
    forall x y : A,
      q180345x_map (q180345x_add RA x y) =
      q180345x_add RK (q180345x_map x) (q180345x_map y);
  q180345x_map_mul :
    forall x y : A,
      q180345x_map (q180345x_mul RA x y) =
      q180345x_mul RK (q180345x_map x) (q180345x_map y)
}.

Arguments q180345x_map {A K RA RK} _ _.

Definition q180345x_divides
    {A : Type}
    (R : q180345x_commutative_ring A)
    (a b : A) : Prop :=
  exists c : A, b = q180345x_mul R a c.

Definition q180345x_unit
    {A : Type}
    (R : q180345x_commutative_ring A)
    (u : A) : Prop :=
  exists v : A,
    q180345x_mul R u v = q180345x_one R.

Definition q180345x_associated
    {A : Type}
    (R : q180345x_commutative_ring A)
    (x y : A) : Prop :=
  exists u : A,
    q180345x_unit R u /\
    x = q180345x_mul R u y.

Definition q180345x_irreducible
    {A : Type}
    (R : q180345x_commutative_ring A)
    (p : A) : Prop :=
  p <> q180345x_zero R /\
  ~ q180345x_unit R p /\
  forall x y : A,
    p = q180345x_mul R x y ->
    q180345x_unit R x \/ q180345x_unit R y.

Definition q180345x_prime
    {A : Type}
    (R : q180345x_commutative_ring A)
    (p : A) : Prop :=
  p <> q180345x_zero R /\
  ~ q180345x_unit R p /\
  forall x y : A,
    q180345x_divides R p (q180345x_mul R x y) ->
    q180345x_divides R p x \/ q180345x_divides R p y.

Fixpoint q180345x_product
    {A : Type}
    (R : q180345x_commutative_ring A)
    (xs : list A) : A :=
  match xs with
  | [] => q180345x_one R
  | x :: rest =>
      q180345x_mul R x (q180345x_product R rest)
  end.

Record q180345x_unique_factorization_monoid
    {A : Type}
    (R : q180345x_commutative_ring A) : Type := {
  q180345x_factorization :
    forall x : A,
      x <> q180345x_zero R ->
      exists factors : list A,
        Forall (q180345x_irreducible R) factors /\
        q180345x_associated R x (q180345x_product R factors);
  q180345x_irreducible_is_prime :
    forall p : A,
      q180345x_irreducible R p ->
      q180345x_prime R p
}.

Record q180345x_fraction_field
    {A K : Type}
    (D : q180345x_integral_domain A)
    (F : q180345x_field K)
    (embed :
      q180345x_ring_hom
        (q180345x_domain_ring D)
        (q180345x_field_ring F)) : Type := {
  q180345x_map_injective :
    forall x y : A,
      q180345x_map embed x = q180345x_map embed y ->
      x = y;
  q180345x_every_element_is_fraction :
    forall r : K,
      exists numerator denominator : A,
        denominator <>
          q180345x_zero (q180345x_domain_ring D) /\
        q180345x_map embed numerator =
          q180345x_mul
            (q180345x_field_ring F)
            r (q180345x_map embed denominator)
}.

Record q180345x_polynomial
    {A : Type}
    (R : q180345x_commutative_ring A) : Type := {
  q180345x_coefficient : nat -> A;
  q180345x_degree : nat;
  q180345x_degree_correct :
    ((forall n : nat,
        q180345x_coefficient n = q180345x_zero R) /\
      q180345x_degree = O) \/
    (q180345x_coefficient q180345x_degree <>
       q180345x_zero R /\
     forall n : nat,
       (q180345x_degree < n)%nat ->
       q180345x_coefficient n = q180345x_zero R)
}.

Arguments q180345x_coefficient {A R} _ _.
Arguments q180345x_degree {A R} _.

Fixpoint q180345x_evaluate_from
    {A K : Type}
    {RA : q180345x_commutative_ring A}
    {RK : q180345x_commutative_ring K}
    (embed : q180345x_ring_hom RA RK)
    (p : q180345x_polynomial RA)
    (r : K)
    (start count : nat) : K :=
  match count with
  | O => q180345x_map embed (q180345x_coefficient p start)
  | S remaining =>
      q180345x_add RK
        (q180345x_map embed (q180345x_coefficient p start))
        (q180345x_mul RK r
          (q180345x_evaluate_from
            embed p r (S start) remaining))
  end.

Definition q180345x_evaluate
    {A K : Type}
    {RA : q180345x_commutative_ring A}
    {RK : q180345x_commutative_ring K}
    (embed : q180345x_ring_hom RA RK)
    (p : q180345x_polynomial RA)
    (r : K) : K :=
  q180345x_evaluate_from
    embed p r O (q180345x_degree p).

Definition q180345x_monic
    {A : Type}
    {R : q180345x_commutative_ring A}
    (p : q180345x_polynomial R) : Prop :=
  q180345x_coefficient p (q180345x_degree p) =
  q180345x_one R.

Definition q180345x_is_root
    {A K : Type}
    {RA : q180345x_commutative_ring A}
    {RK : q180345x_commutative_ring K}
    (embed : q180345x_ring_hom RA RK)
    (p : q180345x_polynomial RA)
    (r : K) : Prop :=
  q180345x_evaluate embed p r = q180345x_zero RK.

Definition q180345x_is_integer
    {A K : Type}
    {RA : q180345x_commutative_ring A}
    {RK : q180345x_commutative_ring K}
    (embed : q180345x_ring_hom RA RK)
    (r : K) : Prop :=
  exists a : A, r = q180345x_map embed a.

Theorem isInteger_of_is_root_of_monic :
  forall
    (A K : Type)
    (D : q180345x_integral_domain A)
    (U :
      q180345x_unique_factorization_monoid
        (q180345x_domain_ring D))
    (F : q180345x_field K)
    (embed :
      q180345x_ring_hom
        (q180345x_domain_ring D)
        (q180345x_field_ring F))
    (FF : q180345x_fraction_field D F embed)
    (p : q180345x_polynomial (q180345x_domain_ring D))
    (r : K),
    q180345x_monic p ->
    q180345x_is_root embed p r ->
    q180345x_is_integer embed r.
Admitted.
