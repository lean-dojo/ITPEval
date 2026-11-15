(*
  Statement-only formalization of Thousand Theorems corpus artifact Q6783821
  (thousand-theorems__rocq__Q6783821), "Mason–Stothers theorem": for three
  nonzero coprime polynomials over a field whose sum is zero, the degrees are
  bounded by the degree of the product's radical unless all three formal
  derivatives vanish. This file contains no proof.
*)

From Stdlib Require Import Lists.List Arith.PeanoNat.

Import ListNotations.

Record q6783821_field (K : Type) : Type := {
  q6783821_zero : K;
  q6783821_one : K;
  q6783821_add : K -> K -> K;
  q6783821_mul : K -> K -> K;
  q6783821_opp : K -> K;
  q6783821_inv : K -> K;
  q6783821_eq_dec : forall x y : K, {x = y} + {x <> y};
  q6783821_one_ne_zero : q6783821_one <> q6783821_zero;
  q6783821_add_assoc :
    forall x y z : K,
      q6783821_add x (q6783821_add y z) =
      q6783821_add (q6783821_add x y) z;
  q6783821_add_comm :
    forall x y : K,
      q6783821_add x y = q6783821_add y x;
  q6783821_add_zero :
    forall x : K,
      q6783821_add x q6783821_zero = x;
  q6783821_add_opp :
    forall x : K,
      q6783821_add x (q6783821_opp x) = q6783821_zero;
  q6783821_mul_assoc :
    forall x y z : K,
      q6783821_mul x (q6783821_mul y z) =
      q6783821_mul (q6783821_mul x y) z;
  q6783821_mul_comm :
    forall x y : K,
      q6783821_mul x y = q6783821_mul y x;
  q6783821_mul_one :
    forall x : K,
      q6783821_mul x q6783821_one = x;
  q6783821_mul_add :
    forall x y z : K,
      q6783821_mul x (q6783821_add y z) =
      q6783821_add
        (q6783821_mul x y)
        (q6783821_mul x z);
  q6783821_mul_inv :
    forall x : K,
      x <> q6783821_zero ->
      q6783821_mul x (q6783821_inv x) = q6783821_one;
  q6783821_inv_zero :
    q6783821_inv q6783821_zero = q6783821_zero
}.

Arguments q6783821_zero {K} _.
Arguments q6783821_one {K} _.
Arguments q6783821_add {K} _ _ _.
Arguments q6783821_mul {K} _ _ _.
Arguments q6783821_opp {K} _ _.
Arguments q6783821_inv {K} _ _.
Arguments q6783821_eq_dec {K} _ _ _.

Definition q6783821_polynomial (K : Type) : Type := list K.

Fixpoint q6783821_drop_leading_zeros
    {K : Type} (F : q6783821_field K)
    (p : q6783821_polynomial K) : q6783821_polynomial K :=
  match p with
  | [] => []
  | a :: rest =>
      if q6783821_eq_dec F a (q6783821_zero F)
      then q6783821_drop_leading_zeros F rest
      else p
  end.

Definition q6783821_normalize
    {K : Type} (F : q6783821_field K)
    (p : q6783821_polynomial K) : q6783821_polynomial K :=
  rev (q6783821_drop_leading_zeros F (rev p)).

Definition q6783821_poly_eq
    {K : Type} (F : q6783821_field K)
    (p q : q6783821_polynomial K) : Prop :=
  q6783821_normalize F p = q6783821_normalize F q.

Definition q6783821_poly_zero {K : Type} : q6783821_polynomial K := [].

Definition q6783821_poly_one
    {K : Type} (F : q6783821_field K) : q6783821_polynomial K :=
  [q6783821_one F].

Fixpoint q6783821_raw_add
    {K : Type} (F : q6783821_field K)
    (p q : q6783821_polynomial K) : q6783821_polynomial K :=
  match p, q with
  | [], _ => q
  | _, [] => p
  | a :: ps, b :: qs =>
      q6783821_add F a b :: q6783821_raw_add F ps qs
  end.

Definition q6783821_poly_add
    {K : Type} (F : q6783821_field K)
    (p q : q6783821_polynomial K) : q6783821_polynomial K :=
  q6783821_normalize F (q6783821_raw_add F p q).

Fixpoint q6783821_raw_scale
    {K : Type} (F : q6783821_field K)
    (c : K) (p : q6783821_polynomial K) : q6783821_polynomial K :=
  match p with
  | [] => []
  | a :: rest =>
      q6783821_mul F c a :: q6783821_raw_scale F c rest
  end.

Definition q6783821_poly_scale
    {K : Type} (F : q6783821_field K)
    (c : K) (p : q6783821_polynomial K) : q6783821_polynomial K :=
  q6783821_normalize F (q6783821_raw_scale F c p).

Fixpoint q6783821_raw_mul
    {K : Type} (F : q6783821_field K)
    (p q : q6783821_polynomial K) : q6783821_polynomial K :=
  match p with
  | [] => []
  | a :: rest =>
      q6783821_raw_add F
        (q6783821_raw_scale F a q)
        (q6783821_zero F :: q6783821_raw_mul F rest q)
  end.

Definition q6783821_poly_mul
    {K : Type} (F : q6783821_field K)
    (p q : q6783821_polynomial K) : q6783821_polynomial K :=
  q6783821_normalize F (q6783821_raw_mul F p q).

Fixpoint q6783821_nat_scalar
    {K : Type} (F : q6783821_field K) (n : nat) : K :=
  match n with
  | O => q6783821_zero F
  | S m => q6783821_add F (q6783821_one F) (q6783821_nat_scalar F m)
  end.

Fixpoint q6783821_derivative_aux
    {K : Type} (F : q6783821_field K)
    (n : nat) (p : q6783821_polynomial K) : q6783821_polynomial K :=
  match p with
  | [] => []
  | a :: rest =>
      q6783821_mul F (q6783821_nat_scalar F n) a
        :: q6783821_derivative_aux F (S n) rest
  end.

Definition q6783821_derivative
    {K : Type} (F : q6783821_field K)
    (p : q6783821_polynomial K) : q6783821_polynomial K :=
  match p with
  | [] => []
  | _ :: rest =>
      q6783821_normalize F (q6783821_derivative_aux F 1 rest)
  end.

Definition q6783821_nat_degree
    {K : Type} (F : q6783821_field K)
    (p : q6783821_polynomial K) : nat :=
  Nat.pred (length (q6783821_normalize F p)).

Definition q6783821_poly_nonzero
    {K : Type} (F : q6783821_field K)
    (p : q6783821_polynomial K) : Prop :=
  ~ q6783821_poly_eq F p q6783821_poly_zero.

Fixpoint q6783821_poly_pow
    {K : Type} (F : q6783821_field K)
    (p : q6783821_polynomial K) (n : nat) : q6783821_polynomial K :=
  match n with
  | O => q6783821_poly_one F
  | S m => q6783821_poly_mul F p (q6783821_poly_pow F p m)
  end.

Definition q6783821_poly_unit
    {K : Type} (F : q6783821_field K)
    (p : q6783821_polynomial K) : Prop :=
  exists c : K,
    c <> q6783821_zero F /\
    q6783821_poly_eq F p [c].

Definition q6783821_irreducible
    {K : Type} (F : q6783821_field K)
    (p : q6783821_polynomial K) : Prop :=
  q6783821_poly_nonzero F p /\
  ~ q6783821_poly_unit F p /\
  forall q r : q6783821_polynomial K,
    q6783821_poly_eq F p (q6783821_poly_mul F q r) ->
    q6783821_poly_unit F q \/ q6783821_poly_unit F r.

Definition q6783821_associate
    {K : Type} (F : q6783821_field K)
    (p q : q6783821_polynomial K) : Prop :=
  exists c : K,
    c <> q6783821_zero F /\
    q6783821_poly_eq F p (q6783821_poly_scale F c q).

Fixpoint q6783821_pairwise_nonassociate
    {K : Type} (F : q6783821_field K)
    (factors : list (q6783821_polynomial K)) : Prop :=
  match factors with
  | [] => True
  | p :: rest =>
      (forall q : q6783821_polynomial K,
        In q rest -> ~ q6783821_associate F p q) /\
      q6783821_pairwise_nonassociate F rest
  end.

Fixpoint q6783821_all_positive (multiplicities : list nat) : Prop :=
  match multiplicities with
  | [] => True
  | n :: rest => (0 < n)%nat /\ q6783821_all_positive rest
  end.

Fixpoint q6783821_factor_power_product
    {K : Type} (F : q6783821_field K)
    (factors : list (q6783821_polynomial K))
    (multiplicities : list nat) : q6783821_polynomial K :=
  match factors, multiplicities with
  | p :: ps, n :: ns =>
      q6783821_poly_mul F
        (q6783821_poly_pow F p n)
        (q6783821_factor_power_product F ps ns)
  | _, _ => q6783821_poly_one F
  end.

Fixpoint q6783821_sum_degrees
    {K : Type} (F : q6783821_field K)
    (factors : list (q6783821_polynomial K)) : nat :=
  match factors with
  | [] => 0
  | p :: rest =>
      q6783821_nat_degree F p + q6783821_sum_degrees F rest
  end.

Definition q6783821_radical_degree
    {K : Type} (F : q6783821_field K)
    (p : q6783821_polynomial K) (n : nat) : Prop :=
  exists (unit_coefficient : K)
         (factors : list (q6783821_polynomial K))
         (multiplicities : list nat),
    unit_coefficient <> q6783821_zero F /\
    length factors = length multiplicities /\
    q6783821_all_positive multiplicities /\
    Forall (q6783821_irreducible F) factors /\
    q6783821_pairwise_nonassociate F factors /\
    q6783821_poly_eq F p
      (q6783821_poly_scale F unit_coefficient
        (q6783821_factor_power_product F factors multiplicities)) /\
    n = q6783821_sum_degrees F factors.

Definition q6783821_is_coprime
    {K : Type} (F : q6783821_field K)
    (p q : q6783821_polynomial K) : Prop :=
  exists x y : q6783821_polynomial K,
    q6783821_poly_eq F
      (q6783821_poly_add F
        (q6783821_poly_mul F x p)
        (q6783821_poly_mul F y q))
      (q6783821_poly_one F).

Theorem q6783821_polynomial_abc :
  forall (K : Type)
         (F : q6783821_field K)
         (a b c : q6783821_polynomial K),
    q6783821_poly_nonzero F a ->
    q6783821_poly_nonzero F b ->
    q6783821_poly_nonzero F c ->
    q6783821_is_coprime F a b ->
    q6783821_poly_eq F
      (q6783821_poly_add F (q6783821_poly_add F a b) c)
      q6783821_poly_zero ->
    (exists radical_degree : nat,
      q6783821_radical_degree F
        (q6783821_poly_mul F (q6783821_poly_mul F a b) c)
        radical_degree /\
      (q6783821_nat_degree F a + 1 <= radical_degree)%nat /\
      (q6783821_nat_degree F b + 1 <= radical_degree)%nat /\
      (q6783821_nat_degree F c + 1 <= radical_degree)%nat) \/
    (q6783821_poly_eq F
       (q6783821_derivative F a) q6783821_poly_zero /\
     q6783821_poly_eq F
       (q6783821_derivative F b) q6783821_poly_zero /\
     q6783821_poly_eq F
       (q6783821_derivative F c) q6783821_poly_zero).
Admitted.
