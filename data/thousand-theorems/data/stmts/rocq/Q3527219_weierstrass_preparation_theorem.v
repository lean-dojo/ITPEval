(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527219
  (thousand-theorems__rocq__Q3527219), "Weierstrass preparation theorem":
  a power series over a complete commutative local ring whose residue-series
  image is nonzero factors as a distinguished polynomial times a unit power
  series. This file contains no proof.
*)

From Stdlib Require Import List Arith.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q3527219_commutative_ring (A : Type) : Type := {
  q3527219_zero : A;
  q3527219_one : A;
  q3527219_add : A -> A -> A;
  q3527219_mul : A -> A -> A;
  q3527219_neg : A -> A;
  q3527219_add_assoc :
    forall x y z : A,
      q3527219_add x (q3527219_add y z) =
      q3527219_add (q3527219_add x y) z;
  q3527219_add_comm :
    forall x y : A, q3527219_add x y = q3527219_add y x;
  q3527219_add_zero :
    forall x : A, q3527219_add x q3527219_zero = x;
  q3527219_add_neg :
    forall x : A,
      q3527219_add x (q3527219_neg x) = q3527219_zero;
  q3527219_mul_assoc :
    forall x y z : A,
      q3527219_mul x (q3527219_mul y z) =
      q3527219_mul (q3527219_mul x y) z;
  q3527219_mul_comm :
    forall x y : A, q3527219_mul x y = q3527219_mul y x;
  q3527219_mul_one :
    forall x : A, q3527219_mul x q3527219_one = x;
  q3527219_left_distrib :
    forall x y z : A,
      q3527219_mul x (q3527219_add y z) =
      q3527219_add
        (q3527219_mul x y) (q3527219_mul x z)
}.

Arguments q3527219_zero {A} _.
Arguments q3527219_one {A} _.
Arguments q3527219_add {A} _ _ _.
Arguments q3527219_mul {A} _ _ _.
Arguments q3527219_neg {A} _ _.

Definition q3527219_sub
    {A : Type} (R : q3527219_commutative_ring A)
    (x y : A) : A :=
  q3527219_add R x (q3527219_neg R y).

Definition q3527219_is_unit
    {A : Type} (R : q3527219_commutative_ring A)
    (x : A) : Prop :=
  exists y : A,
    q3527219_mul R x y = q3527219_one R /\
    q3527219_mul R y x = q3527219_one R.

Record q3527219_ideal
    (A : Type) (R : q3527219_commutative_ring A) : Type := {
  q3527219_ideal_mem : A -> Prop;
  q3527219_ideal_zero :
    q3527219_ideal_mem (q3527219_zero R);
  q3527219_ideal_add :
    forall x y : A,
      q3527219_ideal_mem x ->
      q3527219_ideal_mem y ->
      q3527219_ideal_mem (q3527219_add R x y);
  q3527219_ideal_neg :
    forall x : A,
      q3527219_ideal_mem x ->
      q3527219_ideal_mem (q3527219_neg R x);
  q3527219_ideal_mul :
    forall a x : A,
      q3527219_ideal_mem x ->
      q3527219_ideal_mem (q3527219_mul R a x)
}.

Arguments q3527219_ideal_mem {A R} _ _.

Record q3527219_local_ring
    (A : Type) (R : q3527219_commutative_ring A) : Type := {
  q3527219_maximal_ideal : @q3527219_ideal A R;
  q3527219_maximal_ideal_proper :
    ~ q3527219_ideal_mem q3527219_maximal_ideal
        (q3527219_one R);
  q3527219_unit_of_not_mem_maximal :
    forall x : A,
      ~ q3527219_ideal_mem q3527219_maximal_ideal x ->
      q3527219_is_unit R x
}.

Arguments q3527219_maximal_ideal {A R} _.

Fixpoint q3527219_sum_products
    {A : Type} (R : q3527219_commutative_ring A)
    (terms : list (A * A)) : A :=
  match terms with
  | nil => q3527219_zero R
  | (x, y) :: rest =>
      q3527219_add R
        (q3527219_mul R x y)
        (q3527219_sum_products R rest)
  end.

Definition q3527219_ideal_product
    {A : Type} (R : q3527219_commutative_ring A)
    (I J : A -> Prop) (x : A) : Prop :=
  exists terms : list (A * A),
    Forall
      (fun term : A * A =>
        I (fst term) /\ J (snd term))
      terms /\
    x = q3527219_sum_products R terms.

Fixpoint q3527219_ideal_power
    {A : Type} (R : q3527219_commutative_ring A)
    (I : A -> Prop) (n : nat) : A -> Prop :=
  match n with
  | O => fun _ => True
  | S k =>
      fun x => q3527219_ideal_product R I
        (q3527219_ideal_power R I k) x
  end.

Definition q3527219_congruent_mod_power
    {A : Type} (R : q3527219_commutative_ring A)
    (I : @q3527219_ideal A R)
    (n : nat) (x y : A) : Prop :=
  q3527219_ideal_power R (q3527219_ideal_mem I) n
    (q3527219_sub R x y).

Record q3527219_is_adic_complete
    {A : Type} (R : q3527219_commutative_ring A)
    (I : @q3527219_ideal A R) : Prop := {
  q3527219_adic_hausdorff :
    forall x : A,
      (forall n : nat,
        @q3527219_congruent_mod_power A R I n x
          (q3527219_zero R)) ->
      x = q3527219_zero R;
  q3527219_adic_precomplete :
    forall sequence : nat -> A,
      (forall m n : nat,
        m <= n ->
        @q3527219_congruent_mod_power A R I m
          (sequence m) (sequence n)) ->
      exists limit : A,
        forall n : nat,
          @q3527219_congruent_mod_power A R I n
            (sequence n) limit
}.

Definition q3527219_power_series (A : Type) : Type :=
  nat -> A.

Definition q3527219_power_series_equal
    {A : Type} (p q : q3527219_power_series A) : Prop :=
  forall n : nat, p n = q n.

Definition q3527219_power_series_one
    {A : Type} (R : q3527219_commutative_ring A) :
    q3527219_power_series A :=
  fun n =>
    match n with
    | O => q3527219_one R
    | S _ => q3527219_zero R
    end.

Fixpoint q3527219_power_series_mul_coeff
    {A : Type} (R : q3527219_commutative_ring A)
    (p q : q3527219_power_series A) (n : nat) : A :=
  match n with
  | O => q3527219_mul R (p O) (q O)
  | S k =>
      q3527219_add R
        (q3527219_power_series_mul_coeff R p
          (fun j => q (S j)) k)
        (q3527219_mul R (p (S k)) (q O))
  end.

Definition q3527219_power_series_mul
    {A : Type} (R : q3527219_commutative_ring A)
    (p q : q3527219_power_series A) :
    q3527219_power_series A :=
  fun n => q3527219_power_series_mul_coeff R p q n.

Definition q3527219_power_series_unit
    {A : Type} (R : q3527219_commutative_ring A)
    (h : q3527219_power_series A) : Prop :=
  exists inverse : q3527219_power_series A,
    q3527219_power_series_equal
      (q3527219_power_series_mul R h inverse)
      (q3527219_power_series_one R) /\
    q3527219_power_series_equal
      (q3527219_power_series_mul R inverse h)
      (q3527219_power_series_one R).

Record q3527219_polynomial
    (A : Type) (R : q3527219_commutative_ring A) : Type := {
  q3527219_polynomial_coeff : nat -> A;
  q3527219_polynomial_finite :
    exists bound : nat,
      forall n : nat,
        bound < n ->
        q3527219_polynomial_coeff n = q3527219_zero R
}.

Arguments q3527219_polynomial_coeff {A R} _ _.

Definition q3527219_polynomial_to_power_series
    {A : Type} {R : q3527219_commutative_ring A}
    (f : @q3527219_polynomial A R) :
    q3527219_power_series A :=
  q3527219_polynomial_coeff f.

Definition q3527219_is_distinguished_at
    {A : Type} (R : q3527219_commutative_ring A)
    (I : @q3527219_ideal A R)
    (f : @q3527219_polynomial A R) : Prop :=
  exists degree : nat,
    q3527219_polynomial_coeff f degree = q3527219_one R /\
    (forall n : nat,
      degree < n ->
      q3527219_polynomial_coeff f n = q3527219_zero R) /\
    forall n : nat,
      n < degree ->
      q3527219_ideal_mem I
        (q3527219_polynomial_coeff f n).

Definition q3527219_is_weierstrass_factorization
    {A : Type} (R : q3527219_commutative_ring A)
    (I : @q3527219_ideal A R)
    (g : q3527219_power_series A)
    (f : @q3527219_polynomial A R)
    (h : q3527219_power_series A) : Prop :=
  @q3527219_is_distinguished_at A R I f /\
  q3527219_power_series_unit R h /\
  q3527219_power_series_equal g
    (q3527219_power_series_mul R
      (q3527219_polynomial_to_power_series f) h).

Theorem PowerSeries_exists_isWeierstrassFactorization :
  forall (A : Type)
         (R : q3527219_commutative_ring A)
         (L : @q3527219_local_ring A R),
    @q3527219_is_adic_complete A R
      (q3527219_maximal_ideal L) ->
    forall g : q3527219_power_series A,
      ~ (forall n : nat,
        q3527219_ideal_mem (q3527219_maximal_ideal L) (g n)) ->
      exists (f : @q3527219_polynomial A R)
             (h : q3527219_power_series A),
        @q3527219_is_weierstrass_factorization A R
          (q3527219_maximal_ideal L) g f h.
Admitted.
