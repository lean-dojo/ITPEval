(*
  Statement-only formalization of Thousand Theorems corpus artifact Q720469
  (thousand-theorems__rocq__Q720469), "Chevalley–Warning theorem": over a
  finite field of characteristic p, if the sum of the total degrees of a
  finite family of multivariate polynomials is smaller than the number of
  variables, then p divides the number of their common zeros. This file
  contains no proof.
*)

From Stdlib Require Import List Arith.PeanoNat.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q720469_finite_type (A : Type) : Type := {
  q720469_enum : list A;
  q720469_enum_complete :
    forall x : A, In x q720469_enum;
  q720469_enum_nodup :
    NoDup q720469_enum
}.

Arguments q720469_enum {A} _.

Definition q720469_card
    {A : Type} (FA : q720469_finite_type A) : nat :=
  length (q720469_enum FA).

Record q720469_field (K : Type) : Type := {
  q720469_zero : K;
  q720469_one : K;
  q720469_add : K -> K -> K;
  q720469_mul : K -> K -> K;
  q720469_neg : K -> K;
  q720469_inv : K -> K;
  q720469_eq_dec :
    forall x y : K, {x = y} + {x <> y};
  q720469_add_assoc :
    forall x y z : K,
      q720469_add x (q720469_add y z) =
      q720469_add (q720469_add x y) z;
  q720469_add_comm :
    forall x y : K,
      q720469_add x y = q720469_add y x;
  q720469_add_zero :
    forall x : K,
      q720469_add x q720469_zero = x;
  q720469_add_neg :
    forall x : K,
      q720469_add x (q720469_neg x) = q720469_zero;
  q720469_mul_assoc :
    forall x y z : K,
      q720469_mul x (q720469_mul y z) =
      q720469_mul (q720469_mul x y) z;
  q720469_mul_comm :
    forall x y : K,
      q720469_mul x y = q720469_mul y x;
  q720469_mul_one :
    forall x : K,
      q720469_mul x q720469_one = x;
  q720469_left_distrib :
    forall x y z : K,
      q720469_mul x (q720469_add y z) =
      q720469_add
        (q720469_mul x y) (q720469_mul x z);
  q720469_mul_inv :
    forall x : K,
      x <> q720469_zero ->
      q720469_mul x (q720469_inv x) = q720469_one;
  q720469_nontrivial :
    q720469_zero <> q720469_one
}.

Arguments q720469_zero {K} _.
Arguments q720469_one {K} _.
Arguments q720469_add {K} _ _ _.
Arguments q720469_mul {K} _ _ _.
Arguments q720469_neg {K} _ _.
Arguments q720469_inv {K} _ _.
Arguments q720469_eq_dec {K} _ _ _.

Fixpoint q720469_nat_cast
    {K : Type} (FK : q720469_field K) (n : nat) : K :=
  match n with
  | O => q720469_zero FK
  | S k =>
      q720469_add FK (q720469_nat_cast FK k) (q720469_one FK)
  end.

Definition q720469_has_characteristic
    {K : Type} (FK : q720469_field K) (p : nat) : Prop :=
  forall n : nat,
    q720469_nat_cast FK n = q720469_zero FK <->
    Nat.divide p n.

Definition q720469_monomial (Var : Type) : Type :=
  Var -> nat.

Fixpoint q720469_monomial_eqb_on
    {Var : Type} (variables : list Var)
    (a b : q720469_monomial Var) : bool :=
  match variables with
  | nil => true
  | variable :: rest =>
      Nat.eqb (a variable) (b variable) &&
      q720469_monomial_eqb_on rest a b
  end.

Definition q720469_monomial_eqb
    {Var : Type} (FVar : q720469_finite_type Var)
    (a b : q720469_monomial Var) : bool :=
  q720469_monomial_eqb_on (q720469_enum FVar) a b.

Fixpoint q720469_nat_sum (values : list nat) : nat :=
  match values with
  | nil => O
  | value :: rest => value + q720469_nat_sum rest
  end.

Definition q720469_monomial_degree
    {Var : Type} (FVar : q720469_finite_type Var)
    (m : q720469_monomial Var) : nat :=
  q720469_nat_sum (map m (q720469_enum FVar)).

Definition q720469_polynomial (Var K : Type) : Type :=
  list (q720469_monomial Var * K).

Fixpoint q720469_polynomial_coefficient
    {Var K : Type}
    (FVar : q720469_finite_type Var)
    (FK : q720469_field K)
    (polynomial : q720469_polynomial Var K)
    (m : q720469_monomial Var) : K :=
  match polynomial with
  | nil => q720469_zero FK
  | (n, coefficient) :: rest =>
      if q720469_monomial_eqb FVar n m
      then q720469_add FK coefficient
        (q720469_polynomial_coefficient FVar FK rest m)
      else q720469_polynomial_coefficient FVar FK rest m
  end.

Fixpoint q720469_total_degree_over
    {Var K : Type}
    (FVar : q720469_finite_type Var)
    (FK : q720469_field K)
    (polynomial remaining : q720469_polynomial Var K) : nat :=
  match remaining with
  | nil => O
  | (m, _) :: rest =>
      if q720469_eq_dec FK
           (q720469_polynomial_coefficient FVar FK polynomial m)
           (q720469_zero FK)
      then q720469_total_degree_over FVar FK polynomial rest
      else Nat.max
        (q720469_monomial_degree FVar m)
        (q720469_total_degree_over FVar FK polynomial rest)
  end.

Definition q720469_total_degree
    {Var K : Type}
    (FVar : q720469_finite_type Var)
    (FK : q720469_field K)
    (polynomial : q720469_polynomial Var K) : nat :=
  q720469_total_degree_over FVar FK polynomial polynomial.

Fixpoint q720469_power
    {K : Type} (FK : q720469_field K)
    (x : K) (n : nat) : K :=
  match n with
  | O => q720469_one FK
  | S k =>
      q720469_mul FK x (q720469_power FK x k)
  end.

Fixpoint q720469_monomial_value_on
    {Var K : Type}
    (FK : q720469_field K)
    (variables : list Var)
    (point : Var -> K)
    (m : q720469_monomial Var) : K :=
  match variables with
  | nil => q720469_one FK
  | variable :: rest =>
      q720469_mul FK
        (q720469_power FK (point variable) (m variable))
        (q720469_monomial_value_on FK rest point m)
  end.

Definition q720469_monomial_value
    {Var K : Type}
    (FVar : q720469_finite_type Var)
    (FK : q720469_field K)
    (point : Var -> K)
    (m : q720469_monomial Var) : K :=
  q720469_monomial_value_on
    FK (q720469_enum FVar) point m.

Fixpoint q720469_evaluate
    {Var K : Type}
    (FVar : q720469_finite_type Var)
    (FK : q720469_field K)
    (point : Var -> K)
    (polynomial : q720469_polynomial Var K) : K :=
  match polynomial with
  | nil => q720469_zero FK
  | (m, coefficient) :: rest =>
      q720469_add FK
        (q720469_mul FK coefficient
          (q720469_monomial_value FVar FK point m))
        (q720469_evaluate FVar FK point rest)
  end.

Fixpoint q720469_sum_total_degrees
    {Index Var K : Type}
    (FVar : q720469_finite_type Var)
    (FK : q720469_field K)
    (family : Index -> q720469_polynomial Var K)
    (indices : list Index) : nat :=
  match indices with
  | nil => O
  | index :: rest =>
      q720469_total_degree FVar FK (family index) +
      q720469_sum_total_degrees FVar FK family rest
  end.

Fixpoint q720469_common_zero_b
    {Index Var K : Type}
    (FVar : q720469_finite_type Var)
    (FK : q720469_field K)
    (family : Index -> q720469_polynomial Var K)
    (indices : list Index)
    (point : Var -> K) : bool :=
  match indices with
  | nil => true
  | index :: rest =>
      if q720469_eq_dec FK
           (q720469_evaluate FVar FK point (family index))
           (q720469_zero FK)
      then q720469_common_zero_b FVar FK family rest point
      else false
  end.

Definition q720469_number_of_common_zeros
    {Index Var K : Type}
    (FPoints : q720469_finite_type (Var -> K))
    (FVar : q720469_finite_type Var)
    (FK : q720469_field K)
    (family : Index -> q720469_polynomial Var K)
    (indices : list Index) : nat :=
  length
    (filter
      (q720469_common_zero_b FVar FK family indices)
      (q720469_enum FPoints)).

Theorem char_dvd_card_solutions_of_sum_lt :
  forall
    (K Var Index : Type)
    (FK : q720469_field K)
    (FK_finite : q720469_finite_type K)
    (FVar : q720469_finite_type Var)
    (FPoints : q720469_finite_type (Var -> K))
    (p : nat),
    q720469_has_characteristic FK p ->
    forall
      (indices : list Index)
      (family : Index -> q720469_polynomial Var K),
      NoDup indices ->
      q720469_sum_total_degrees FVar FK family indices <
        q720469_card FVar ->
      Nat.divide p
        (q720469_number_of_common_zeros
          FPoints FVar FK family indices).
Admitted.
