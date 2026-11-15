(*
  Statement-only formalization of Thousand Theorems corpus artifact Q4830725
  (thousand-theorems__rocq__Q4830725), "Ax-Grothendieck theorem": over an
  algebraically closed field with finitely many variables, every injective
  polynomial self-map preserving the zero locus of an ideal is surjective on
  that zero locus. This file contains no proof.
*)

From Stdlib Require Import List Arith Bool.

Set Universe Polymorphism.
Set Implicit Arguments.

Import ListNotations.

Record q4830725_field (K : Type) : Type := {
  q4830725_zero : K;
  q4830725_one : K;
  q4830725_add : K -> K -> K;
  q4830725_mul : K -> K -> K;
  q4830725_neg : K -> K;
  q4830725_inv : K -> K;
  q4830725_add_assoc :
    forall x y z : K,
      q4830725_add x (q4830725_add y z) =
      q4830725_add (q4830725_add x y) z;
  q4830725_add_comm :
    forall x y : K, q4830725_add x y = q4830725_add y x;
  q4830725_add_zero :
    forall x : K, q4830725_add x q4830725_zero = x;
  q4830725_add_neg :
    forall x : K, q4830725_add x (q4830725_neg x) = q4830725_zero;
  q4830725_mul_assoc :
    forall x y z : K,
      q4830725_mul x (q4830725_mul y z) =
      q4830725_mul (q4830725_mul x y) z;
  q4830725_mul_comm :
    forall x y : K, q4830725_mul x y = q4830725_mul y x;
  q4830725_mul_one :
    forall x : K, q4830725_mul x q4830725_one = x;
  q4830725_left_distrib :
    forall x y z : K,
      q4830725_mul x (q4830725_add y z) =
      q4830725_add
        (q4830725_mul x y) (q4830725_mul x z);
  q4830725_mul_inv :
    forall x : K, x <> q4830725_zero ->
      q4830725_mul x (q4830725_inv x) = q4830725_one;
  q4830725_nontrivial : q4830725_zero <> q4830725_one
}.

Arguments q4830725_zero {K} _.
Arguments q4830725_one {K} _.
Arguments q4830725_add {K} _ _ _.
Arguments q4830725_mul {K} _ _ _.
Arguments q4830725_neg {K} _ _.
Arguments q4830725_inv {K} _ _.

Fixpoint q4830725_univariate_eval
    {K : Type} (FK : q4830725_field K)
    (coefficients : list K) (x : K) : K :=
  match coefficients with
  | [] => q4830725_zero FK
  | c :: rest =>
      q4830725_add FK c
        (q4830725_mul FK x
          (q4830725_univariate_eval FK rest x))
  end.

Fixpoint q4830725_some_nonzero
    {K : Type} (FK : q4830725_field K)
    (coefficients : list K) : Prop :=
  match coefficients with
  | [] => False
  | c :: rest =>
      c <> q4830725_zero FK \/
      q4830725_some_nonzero FK rest
  end.

Definition q4830725_univariate_nonconstant
    {K : Type} (FK : q4830725_field K)
    (coefficients : list K) : Prop :=
  match coefficients with
  | [] => False
  | _ :: positive_degree_coefficients =>
      q4830725_some_nonzero FK positive_degree_coefficients
  end.

Definition q4830725_is_algebraically_closed
    {K : Type} (FK : q4830725_field K) : Prop :=
  forall coefficients : list K,
    q4830725_univariate_nonconstant FK coefficients ->
    exists x : K,
      q4830725_univariate_eval FK coefficients x =
      q4830725_zero FK.

Record q4830725_finite_index (Iota : Type) : Type := {
  q4830725_enum : list Iota;
  q4830725_enum_complete :
    forall i : Iota, In i q4830725_enum;
  q4830725_enum_nodup : NoDup q4830725_enum
}.

Arguments q4830725_enum {Iota} _.

Definition q4830725_monomial (Iota : Type) : Type := Iota -> nat.

Fixpoint q4830725_monomial_eqb_on
    {Iota : Type} (indices : list Iota)
    (a b : q4830725_monomial Iota) : bool :=
  match indices with
  | [] => true
  | i :: rest =>
      Nat.eqb (a i) (b i) &&
      q4830725_monomial_eqb_on rest a b
  end.

Definition q4830725_monomial_eqb
    {Iota : Type} (FI : q4830725_finite_index Iota)
    (a b : q4830725_monomial Iota) : bool :=
  q4830725_monomial_eqb_on (q4830725_enum FI) a b.

Definition q4830725_monomial_zero
    {Iota : Type} : q4830725_monomial Iota :=
  fun _ => 0.

Definition q4830725_monomial_add
    {Iota : Type}
    (a b : q4830725_monomial Iota) : q4830725_monomial Iota :=
  fun i => a i + b i.

Definition q4830725_polynomial (Iota K : Type) : Type :=
  list (q4830725_monomial Iota * K).

Fixpoint q4830725_polynomial_coefficient
    {Iota K : Type}
    (FI : q4830725_finite_index Iota)
    (FK : q4830725_field K)
    (p : q4830725_polynomial Iota K)
    (m : q4830725_monomial Iota) : K :=
  match p with
  | [] => q4830725_zero FK
  | (n, c) :: rest =>
      if q4830725_monomial_eqb FI n m
      then q4830725_add FK c
        (q4830725_polynomial_coefficient FI FK rest m)
      else q4830725_polynomial_coefficient FI FK rest m
  end.

Definition q4830725_polynomial_equiv
    {Iota K : Type}
    (FI : q4830725_finite_index Iota)
    (FK : q4830725_field K)
    (p q : q4830725_polynomial Iota K) : Prop :=
  forall m : q4830725_monomial Iota,
    q4830725_polynomial_coefficient FI FK p m =
    q4830725_polynomial_coefficient FI FK q m.

Definition q4830725_polynomial_zero
    {Iota K : Type} : q4830725_polynomial Iota K :=
  [].

Definition q4830725_polynomial_add
    {Iota K : Type}
    (p q : q4830725_polynomial Iota K) :
    q4830725_polynomial Iota K :=
  p ++ q.

Definition q4830725_polynomial_neg
    {Iota K : Type} (FK : q4830725_field K)
    (p : q4830725_polynomial Iota K) :
    q4830725_polynomial Iota K :=
  map (fun term =>
    (fst term, q4830725_neg FK (snd term))) p.

Definition q4830725_term_mul
    {Iota K : Type} (FK : q4830725_field K)
    (left right : q4830725_monomial Iota * K) :
    q4830725_monomial Iota * K :=
  (q4830725_monomial_add (fst left) (fst right),
   q4830725_mul FK (snd left) (snd right)).

Definition q4830725_polynomial_mul
    {Iota K : Type} (FK : q4830725_field K)
    (p q : q4830725_polynomial Iota K) :
    q4830725_polynomial Iota K :=
  flat_map
    (fun left => map (q4830725_term_mul FK left) q) p.

Record q4830725_ideal
    (Iota K : Type)
    (FI : q4830725_finite_index Iota)
    (FK : q4830725_field K) : Type := {
  q4830725_ideal_mem : q4830725_polynomial Iota K -> Prop;
  q4830725_ideal_respects :
    forall p q : q4830725_polynomial Iota K,
      q4830725_polynomial_equiv FI FK p q ->
      (q4830725_ideal_mem p <-> q4830725_ideal_mem q);
  q4830725_ideal_zero :
    q4830725_ideal_mem q4830725_polynomial_zero;
  q4830725_ideal_add :
    forall p q : q4830725_polynomial Iota K,
      q4830725_ideal_mem p ->
      q4830725_ideal_mem q ->
      q4830725_ideal_mem (q4830725_polynomial_add p q);
  q4830725_ideal_neg :
    forall p : q4830725_polynomial Iota K,
      q4830725_ideal_mem p ->
      q4830725_ideal_mem (q4830725_polynomial_neg FK p);
  q4830725_ideal_mul :
    forall a p : q4830725_polynomial Iota K,
      q4830725_ideal_mem p ->
      q4830725_ideal_mem (q4830725_polynomial_mul FK a p)
}.

Arguments q4830725_ideal_mem {Iota K FI FK} _ _.

Fixpoint q4830725_field_pow
    {K : Type} (FK : q4830725_field K)
    (x : K) (n : nat) : K :=
  match n with
  | 0 => q4830725_one FK
  | S exponent =>
      q4830725_mul FK x
        (q4830725_field_pow FK x exponent)
  end.

Fixpoint q4830725_monomial_value_on
    {Iota K : Type}
    (FK : q4830725_field K)
    (indices : list Iota)
    (point : Iota -> K)
    (m : q4830725_monomial Iota) : K :=
  match indices with
  | [] => q4830725_one FK
  | i :: rest =>
      q4830725_mul FK
        (q4830725_field_pow FK (point i) (m i))
        (q4830725_monomial_value_on FK rest point m)
  end.

Definition q4830725_monomial_value
    {Iota K : Type}
    (FI : q4830725_finite_index Iota)
    (FK : q4830725_field K)
    (point : Iota -> K)
    (m : q4830725_monomial Iota) : K :=
  q4830725_monomial_value_on
    FK (q4830725_enum FI) point m.

Fixpoint q4830725_evaluate
    {Iota K : Type}
    (FI : q4830725_finite_index Iota)
    (FK : q4830725_field K)
    (point : Iota -> K)
    (p : q4830725_polynomial Iota K) : K :=
  match p with
  | [] => q4830725_zero FK
  | (m, c) :: rest =>
      q4830725_add FK
        (q4830725_mul FK c
          (q4830725_monomial_value FI FK point m))
        (q4830725_evaluate FI FK point rest)
  end.

Definition q4830725_zero_locus
    {Iota K : Type}
    (FI : q4830725_finite_index Iota)
    (FK : q4830725_field K)
    (J : q4830725_ideal FI FK)
    (point : Iota -> K) : Prop :=
  forall p : q4830725_polynomial Iota K,
    q4830725_ideal_mem J p ->
    q4830725_evaluate FI FK point p = q4830725_zero FK.

Definition q4830725_polynomial_map
    {Iota K : Type}
    (FI : q4830725_finite_index Iota)
    (FK : q4830725_field K)
    (polynomials : Iota -> q4830725_polynomial Iota K)
    (point : Iota -> K) : Iota -> K :=
  fun i => q4830725_evaluate FI FK point (polynomials i).

Definition q4830725_maps_to_zero_locus
    {Iota K : Type}
    (FI : q4830725_finite_index Iota)
    (FK : q4830725_field K)
  (J : q4830725_ideal FI FK)
    (polynomials : Iota -> q4830725_polynomial Iota K) : Prop :=
  forall point : Iota -> K,
    @q4830725_zero_locus Iota K FI FK J point ->
    @q4830725_zero_locus Iota K FI FK J
      (@q4830725_polynomial_map Iota K FI FK polynomials point).

Definition q4830725_injective_on_zero_locus
    {Iota K : Type}
    (FI : q4830725_finite_index Iota)
    (FK : q4830725_field K)
    (J : q4830725_ideal FI FK)
    (polynomials : Iota -> q4830725_polynomial Iota K) : Prop :=
  forall x y : Iota -> K,
    @q4830725_zero_locus Iota K FI FK J x ->
    @q4830725_zero_locus Iota K FI FK J y ->
    (forall i : Iota,
      @q4830725_polynomial_map Iota K FI FK polynomials x i =
      @q4830725_polynomial_map Iota K FI FK polynomials y i) ->
    forall i : Iota, x i = y i.

Definition q4830725_surjective_on_zero_locus
    {Iota K : Type}
    (FI : q4830725_finite_index Iota)
    (FK : q4830725_field K)
    (J : q4830725_ideal FI FK)
    (polynomials : Iota -> q4830725_polynomial Iota K) : Prop :=
  forall y : Iota -> K,
    @q4830725_zero_locus Iota K FI FK J y ->
    exists x : Iota -> K,
      @q4830725_zero_locus Iota K FI FK J x /\
      forall i : Iota,
        @q4830725_polynomial_map Iota K FI FK polynomials x i = y i.

Theorem ax_grothendieck_zeroLocus :
  forall (K Iota : Type)
         (FK : q4830725_field K)
         (FI : q4830725_finite_index Iota),
    q4830725_is_algebraically_closed FK ->
    forall (J : q4830725_ideal FI FK)
           (polynomials : Iota -> q4830725_polynomial Iota K),
      @q4830725_maps_to_zero_locus Iota K FI FK J polynomials ->
      @q4830725_injective_on_zero_locus Iota K FI FK J polynomials ->
      @q4830725_surjective_on_zero_locus Iota K FI FK J polynomials.
Admitted.
