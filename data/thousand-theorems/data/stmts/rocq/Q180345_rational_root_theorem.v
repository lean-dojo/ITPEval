(*
  Statement-only formalization of Thousand Theorems corpus artifact Q180345
  (thousand-theorems__rocq__Q180345), "Rational root theorem": for a
  polynomial over a unique factorization domain, the reduced numerator of a
  root in its fraction field divides the constant coefficient, and the
  reduced denominator divides the leading coefficient. This file contains no
  proof.
*)

From Stdlib Require Import List Arith.PeanoNat.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q180345_comm_ring (R : Type) : Type := {
  q180345_zero : R;
  q180345_one : R;
  q180345_add : R -> R -> R;
  q180345_mul : R -> R -> R;
  q180345_neg : R -> R;
  q180345_add_assoc :
    forall x y z : R,
      q180345_add x (q180345_add y z) =
      q180345_add (q180345_add x y) z;
  q180345_add_comm :
    forall x y : R, q180345_add x y = q180345_add y x;
  q180345_add_zero :
    forall x : R, q180345_add x q180345_zero = x;
  q180345_add_neg :
    forall x : R, q180345_add x (q180345_neg x) = q180345_zero;
  q180345_mul_assoc :
    forall x y z : R,
      q180345_mul x (q180345_mul y z) =
      q180345_mul (q180345_mul x y) z;
  q180345_mul_comm :
    forall x y : R, q180345_mul x y = q180345_mul y x;
  q180345_mul_one :
    forall x : R, q180345_mul x q180345_one = x;
  q180345_mul_zero :
    forall x : R, q180345_mul x q180345_zero = q180345_zero;
  q180345_left_distrib :
    forall x y z : R,
      q180345_mul x (q180345_add y z) =
      q180345_add (q180345_mul x y) (q180345_mul x z)
}.

Arguments q180345_zero {R} _.
Arguments q180345_one {R} _.
Arguments q180345_add {R} _ _ _.
Arguments q180345_mul {R} _ _ _.
Arguments q180345_neg {R} _ _.

Record q180345_domain
    {R : Type} (RR : q180345_comm_ring R) : Type := {
  q180345_domain_nontrivial :
    q180345_zero RR <> q180345_one RR;
  q180345_no_zero_divisors :
    forall x y : R,
      q180345_mul RR x y = q180345_zero RR ->
      x = q180345_zero RR \/ y = q180345_zero RR
}.

Record q180345_field
    {K : Type} (RK : q180345_comm_ring K) : Type := {
  q180345_inv : K -> K;
  q180345_field_nontrivial :
    q180345_zero RK <> q180345_one RK;
  q180345_mul_inv :
    forall x : K,
      x <> q180345_zero RK ->
      q180345_mul RK x (q180345_inv x) = q180345_one RK
}.

Arguments q180345_inv {K RK} _ _.

Record q180345_ring_hom
    {A K : Type}
    (RA : q180345_comm_ring A)
    (RK : q180345_comm_ring K) : Type := {
  q180345_embed : A -> K;
  q180345_embed_zero :
    q180345_embed (q180345_zero RA) = q180345_zero RK;
  q180345_embed_one :
    q180345_embed (q180345_one RA) = q180345_one RK;
  q180345_embed_add :
    forall a b : A,
      q180345_embed (q180345_add RA a b) =
      q180345_add RK (q180345_embed a) (q180345_embed b);
  q180345_embed_mul :
    forall a b : A,
      q180345_embed (q180345_mul RA a b) =
      q180345_mul RK (q180345_embed a) (q180345_embed b)
}.

Arguments q180345_embed {A K RA RK} _ _.

Definition q180345_divides
    {A : Type} (RA : q180345_comm_ring A) (a b : A) : Prop :=
  exists c : A, b = q180345_mul RA a c.

Definition q180345_is_unit
    {A : Type} (RA : q180345_comm_ring A) (a : A) : Prop :=
  exists b : A, q180345_mul RA a b = q180345_one RA.

Definition q180345_associated
    {A : Type} (RA : q180345_comm_ring A) (a b : A) : Prop :=
  exists u : A,
    q180345_is_unit RA u /\ a = q180345_mul RA u b.

Definition q180345_irreducible
    {A : Type} (RA : q180345_comm_ring A) (p : A) : Prop :=
  p <> q180345_zero RA /\
  ~ q180345_is_unit RA p /\
  forall a b : A,
    p = q180345_mul RA a b ->
    q180345_is_unit RA a \/ q180345_is_unit RA b.

Definition q180345_prime
    {A : Type} (RA : q180345_comm_ring A) (p : A) : Prop :=
  p <> q180345_zero RA /\
  ~ q180345_is_unit RA p /\
  forall a b : A,
    q180345_divides RA p (q180345_mul RA a b) ->
    q180345_divides RA p a \/ q180345_divides RA p b.

Fixpoint q180345_product
    {A : Type} (RA : q180345_comm_ring A)
    (factors : list A) : A :=
  match factors with
  | nil => q180345_one RA
  | factor :: rest =>
      q180345_mul RA factor (q180345_product RA rest)
  end.

Record q180345_unique_factorization_monoid
    {A : Type}
    (RA : q180345_comm_ring A)
    (DA : q180345_domain RA) : Type := {
  q180345_factorization_exists :
    forall a : A,
      a <> q180345_zero RA ->
      exists factors : list A,
        List.Forall (q180345_irreducible RA) factors /\
        q180345_associated RA a (q180345_product RA factors);
  q180345_irreducible_is_prime :
    forall p : A,
      q180345_irreducible RA p ->
      q180345_prime RA p
}.

Record q180345_fraction_field
    {A K : Type}
    (RA : q180345_comm_ring A)
    (DA : q180345_domain RA)
    (RK : q180345_comm_ring K)
    (FK : q180345_field RK)
    (E : q180345_ring_hom RA RK) : Type := {
  q180345_num : K -> A;
  q180345_den : K -> A;
  q180345_embed_injective :
    forall a b : A,
      q180345_embed E a = q180345_embed E b -> a = b;
  q180345_den_nonzero :
    forall r : K, q180345_den r <> q180345_zero RA;
  q180345_num_den_represents :
    forall r : K,
      q180345_embed E (q180345_num r) =
      q180345_mul RK r (q180345_embed E (q180345_den r));
  q180345_num_den_reduced :
    forall (r : K) (d : A),
      q180345_divides RA d (q180345_num r) ->
      q180345_divides RA d (q180345_den r) ->
      q180345_is_unit RA d
}.

Arguments q180345_num {A K RA DA RK FK E} _ _.
Arguments q180345_den {A K RA DA RK FK E} _ _.

Record q180345_polynomial
    {A : Type} (RA : q180345_comm_ring A) : Type := {
  q180345_coeff : nat -> A;
  q180345_nat_degree : nat;
  q180345_coeff_above_degree :
    forall n : nat,
      (q180345_nat_degree < n)%nat ->
      q180345_coeff n = q180345_zero RA;
  q180345_degree_spec :
    q180345_coeff q180345_nat_degree <> q180345_zero RA \/
    (q180345_nat_degree = 0 /\ q180345_coeff 0 = q180345_zero RA)
}.

Arguments q180345_coeff {A RA} _ _.
Arguments q180345_nat_degree {A RA} _.

Definition q180345_leading_coeff
    {A : Type} {RA : q180345_comm_ring A}
    (p : q180345_polynomial RA) : A :=
  q180345_coeff p (q180345_nat_degree p).

Fixpoint q180345_pow
    {K : Type} (RK : q180345_comm_ring K)
    (x : K) (n : nat) : K :=
  match n with
  | 0 => q180345_one RK
  | S exponent =>
      q180345_mul RK x (q180345_pow RK x exponent)
  end.

Fixpoint q180345_eval_terms
    {A K : Type}
    (RA : q180345_comm_ring A)
    (RK : q180345_comm_ring K)
    (E : q180345_ring_hom RA RK)
    (p : q180345_polynomial RA)
    (r : K)
    (degree : nat) : K :=
  match degree with
  | 0 => q180345_embed E (q180345_coeff p 0)
  | S previous =>
      q180345_add RK
        (@q180345_eval_terms A K RA RK E p r previous)
        (q180345_mul RK
          (q180345_embed E (q180345_coeff p (S previous)))
          (q180345_pow RK r (S previous)))
  end.

Definition q180345_aeval
    {A K : Type}
    (RA : q180345_comm_ring A)
    (RK : q180345_comm_ring K)
    (E : q180345_ring_hom RA RK)
    (p : q180345_polynomial RA)
    (r : K) : K :=
  @q180345_eval_terms A K RA RK E p r (q180345_nat_degree p).

Theorem num_dvd_of_is_root :
  forall
    (A K : Type)
    (RA : q180345_comm_ring A)
    (DA : q180345_domain RA)
    (UA : @q180345_unique_factorization_monoid A RA DA)
    (RK : q180345_comm_ring K)
    (FK : q180345_field RK)
    (E : @q180345_ring_hom A K RA RK)
    (FF : @q180345_fraction_field A K RA DA RK FK E)
    (p : @q180345_polynomial A RA)
    (r : K),
    @q180345_aeval A K RA RK E p r = q180345_zero RK ->
    q180345_divides RA
      (q180345_num FF r) (q180345_coeff p 0).
Admitted.

Theorem den_dvd_of_is_root :
  forall
    (A K : Type)
    (RA : q180345_comm_ring A)
    (DA : q180345_domain RA)
    (UA : @q180345_unique_factorization_monoid A RA DA)
    (RK : q180345_comm_ring K)
    (FK : q180345_field RK)
    (E : @q180345_ring_hom A K RA RK)
    (FF : @q180345_fraction_field A K RA DA RK FK E)
    (p : @q180345_polynomial A RA)
    (r : K),
    @q180345_aeval A K RA RK E p r = q180345_zero RK ->
    q180345_divides RA
      (q180345_den FF r) (q180345_leading_coeff p).
Admitted.
