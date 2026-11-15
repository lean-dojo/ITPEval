(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1068976
  (thousand-theorems__rocq__Q1068976), "Hilbert's Nullstellensatz": over an
  algebraically closed field extension, the vanishing ideal of the common
  zero locus of an ideal in a finitely generated multivariate polynomial ring
  is its radical. This file contains no proof.
*)

From Stdlib Require Import List Arith Bool.

Set Universe Polymorphism.
Set Implicit Arguments.

Import ListNotations.

Record q1068976_field (F : Type) : Type := {
  q1068976_zero : F;
  q1068976_one : F;
  q1068976_add : F -> F -> F;
  q1068976_mul : F -> F -> F;
  q1068976_neg : F -> F;
  q1068976_inv : F -> F;
  q1068976_add_assoc :
    forall x y z : F,
      q1068976_add x (q1068976_add y z) =
      q1068976_add (q1068976_add x y) z;
  q1068976_add_comm :
    forall x y : F, q1068976_add x y = q1068976_add y x;
  q1068976_add_zero :
    forall x : F, q1068976_add x q1068976_zero = x;
  q1068976_add_neg :
    forall x : F, q1068976_add x (q1068976_neg x) = q1068976_zero;
  q1068976_mul_assoc :
    forall x y z : F,
      q1068976_mul x (q1068976_mul y z) =
      q1068976_mul (q1068976_mul x y) z;
  q1068976_mul_comm :
    forall x y : F, q1068976_mul x y = q1068976_mul y x;
  q1068976_mul_one :
    forall x : F, q1068976_mul x q1068976_one = x;
  q1068976_left_distrib :
    forall x y z : F,
      q1068976_mul x (q1068976_add y z) =
      q1068976_add
        (q1068976_mul x y) (q1068976_mul x z);
  q1068976_mul_inv :
    forall x : F, x <> q1068976_zero ->
      q1068976_mul x (q1068976_inv x) = q1068976_one;
  q1068976_nontrivial : q1068976_zero <> q1068976_one
}.

Arguments q1068976_zero {F} _.
Arguments q1068976_one {F} _.
Arguments q1068976_add {F} _ _ _.
Arguments q1068976_mul {F} _ _ _.
Arguments q1068976_neg {F} _ _.
Arguments q1068976_inv {F} _ _.

Record q1068976_field_algebra
    (k K : Type)
    (Fk : q1068976_field k)
    (FK : q1068976_field K) : Type := {
  q1068976_embed : k -> K;
  q1068976_embed_zero :
    q1068976_embed (q1068976_zero Fk) = q1068976_zero FK;
  q1068976_embed_one :
    q1068976_embed (q1068976_one Fk) = q1068976_one FK;
  q1068976_embed_add :
    forall a b : k,
      q1068976_embed (q1068976_add Fk a b) =
      q1068976_add FK (q1068976_embed a) (q1068976_embed b);
  q1068976_embed_mul :
    forall a b : k,
      q1068976_embed (q1068976_mul Fk a b) =
      q1068976_mul FK (q1068976_embed a) (q1068976_embed b)
}.

Arguments q1068976_embed {k K Fk FK} _ _.

Fixpoint q1068976_univariate_eval
    {K : Type} (FK : q1068976_field K)
    (coefficients : list K) (x : K) : K :=
  match coefficients with
  | [] => q1068976_zero FK
  | c :: rest =>
      q1068976_add FK c
        (q1068976_mul FK x
          (q1068976_univariate_eval FK rest x))
  end.

Fixpoint q1068976_some_nonzero
    {K : Type} (FK : q1068976_field K)
    (coefficients : list K) : Prop :=
  match coefficients with
  | [] => False
  | c :: rest =>
      c <> q1068976_zero FK \/
      q1068976_some_nonzero FK rest
  end.

Definition q1068976_univariate_nonconstant
    {K : Type} (FK : q1068976_field K)
    (coefficients : list K) : Prop :=
  match coefficients with
  | [] => False
  | _ :: positive_degree_coefficients =>
      q1068976_some_nonzero FK positive_degree_coefficients
  end.

Definition q1068976_is_algebraically_closed
    {K : Type} (FK : q1068976_field K) : Prop :=
  forall coefficients : list K,
    q1068976_univariate_nonconstant FK coefficients ->
    exists x : K,
      q1068976_univariate_eval FK coefficients x =
      q1068976_zero FK.

Record q1068976_finite_index (S : Type) : Type := {
  q1068976_enum : list S;
  q1068976_enum_complete :
    forall s : S, In s q1068976_enum;
  q1068976_enum_nodup : NoDup q1068976_enum
}.

Arguments q1068976_enum {S} _.

Definition q1068976_monomial (S : Type) : Type := S -> nat.

Fixpoint q1068976_monomial_eqb_on
    {S : Type} (indices : list S)
    (a b : q1068976_monomial S) : bool :=
  match indices with
  | [] => true
  | s :: rest =>
      Nat.eqb (a s) (b s) &&
      q1068976_monomial_eqb_on rest a b
  end.

Definition q1068976_monomial_eqb
    {S : Type} (FS : q1068976_finite_index S)
    (a b : q1068976_monomial S) : bool :=
  q1068976_monomial_eqb_on (q1068976_enum FS) a b.

Definition q1068976_monomial_zero
    {S : Type} : q1068976_monomial S :=
  fun _ => 0.

Definition q1068976_monomial_add
    {S : Type}
    (a b : q1068976_monomial S) : q1068976_monomial S :=
  fun s => a s + b s.

Definition q1068976_polynomial (S k : Type) : Type :=
  list (q1068976_monomial S * k).

Fixpoint q1068976_polynomial_coefficient
    {S k : Type}
    (FS : q1068976_finite_index S)
    (Fk : q1068976_field k)
    (p : q1068976_polynomial S k)
    (m : q1068976_monomial S) : k :=
  match p with
  | [] => q1068976_zero Fk
  | (n, c) :: rest =>
      if q1068976_monomial_eqb FS n m
      then q1068976_add Fk c
        (q1068976_polynomial_coefficient FS Fk rest m)
      else q1068976_polynomial_coefficient FS Fk rest m
  end.

Definition q1068976_polynomial_equiv
    {S k : Type}
    (FS : q1068976_finite_index S)
    (Fk : q1068976_field k)
    (p q : q1068976_polynomial S k) : Prop :=
  forall m : q1068976_monomial S,
    q1068976_polynomial_coefficient FS Fk p m =
    q1068976_polynomial_coefficient FS Fk q m.

Definition q1068976_polynomial_zero
    {S k : Type} : q1068976_polynomial S k :=
  [].

Definition q1068976_polynomial_one
    {S k : Type} (Fk : q1068976_field k) :
    q1068976_polynomial S k :=
  [(q1068976_monomial_zero, q1068976_one Fk)].

Definition q1068976_polynomial_add
    {S k : Type}
    (p q : q1068976_polynomial S k) :
    q1068976_polynomial S k :=
  p ++ q.

Definition q1068976_polynomial_neg
    {S k : Type} (Fk : q1068976_field k)
    (p : q1068976_polynomial S k) :
    q1068976_polynomial S k :=
  map (fun term =>
    (fst term, q1068976_neg Fk (snd term))) p.

Definition q1068976_term_mul
    {S k : Type} (Fk : q1068976_field k)
    (left right : q1068976_monomial S * k) :
    q1068976_monomial S * k :=
  (q1068976_monomial_add (fst left) (fst right),
   q1068976_mul Fk (snd left) (snd right)).

Definition q1068976_polynomial_mul
    {S k : Type} (Fk : q1068976_field k)
    (p q : q1068976_polynomial S k) :
    q1068976_polynomial S k :=
  flat_map
    (fun left => map (q1068976_term_mul Fk left) q) p.

Fixpoint q1068976_polynomial_pow
    {S k : Type} (Fk : q1068976_field k)
    (p : q1068976_polynomial S k) (n : nat) :
    q1068976_polynomial S k :=
  match n with
  | 0 => q1068976_polynomial_one Fk
  | S exponent =>
      q1068976_polynomial_mul Fk p
        (q1068976_polynomial_pow Fk p exponent)
  end.

Record q1068976_ideal
    (S k : Type)
    (FS : q1068976_finite_index S)
    (Fk : q1068976_field k) : Type := {
  q1068976_ideal_mem : q1068976_polynomial S k -> Prop;
  q1068976_ideal_respects :
    forall p q : q1068976_polynomial S k,
      q1068976_polynomial_equiv FS Fk p q ->
      (q1068976_ideal_mem p <-> q1068976_ideal_mem q);
  q1068976_ideal_zero :
    q1068976_ideal_mem q1068976_polynomial_zero;
  q1068976_ideal_add :
    forall p q : q1068976_polynomial S k,
      q1068976_ideal_mem p ->
      q1068976_ideal_mem q ->
      q1068976_ideal_mem (q1068976_polynomial_add p q);
  q1068976_ideal_neg :
    forall p : q1068976_polynomial S k,
      q1068976_ideal_mem p ->
      q1068976_ideal_mem (q1068976_polynomial_neg Fk p);
  q1068976_ideal_mul :
    forall a p : q1068976_polynomial S k,
      q1068976_ideal_mem p ->
      q1068976_ideal_mem (q1068976_polynomial_mul Fk a p)
}.

Arguments q1068976_ideal_mem {S k FS Fk} _ _.

Fixpoint q1068976_field_pow
    {F : Type} (FF : q1068976_field F)
    (x : F) (n : nat) : F :=
  match n with
  | 0 => q1068976_one FF
  | S exponent =>
      q1068976_mul FF x
        (q1068976_field_pow FF x exponent)
  end.

Fixpoint q1068976_monomial_value_on
    {S K : Type}
    (FK : q1068976_field K)
    (indices : list S)
    (point : S -> K)
    (m : q1068976_monomial S) : K :=
  match indices with
  | [] => q1068976_one FK
  | s :: rest =>
      q1068976_mul FK
        (q1068976_field_pow FK (point s) (m s))
        (q1068976_monomial_value_on FK rest point m)
  end.

Definition q1068976_monomial_value
    {S K : Type}
    (FS : q1068976_finite_index S)
    (FK : q1068976_field K)
    (point : S -> K)
    (m : q1068976_monomial S) : K :=
  q1068976_monomial_value_on
    FK (q1068976_enum FS) point m.

Fixpoint q1068976_evaluate
    {S k K : Type}
    (FS : q1068976_finite_index S)
    (Fk : q1068976_field k)
    (FK : q1068976_field K)
    (A : q1068976_field_algebra Fk FK)
    (point : S -> K)
    (p : q1068976_polynomial S k) : K :=
  match p with
  | [] => q1068976_zero FK
  | (m, c) :: rest =>
      q1068976_add FK
        (q1068976_mul FK
          (q1068976_embed A c)
          (q1068976_monomial_value FS FK point m))
        (@q1068976_evaluate S k K FS Fk FK A point rest)
  end.

Definition q1068976_zero_locus
    {S k K : Type}
    (FS : q1068976_finite_index S)
    (Fk : q1068976_field k)
    (FK : q1068976_field K)
    (A : q1068976_field_algebra Fk FK)
    (I : q1068976_ideal FS Fk)
    (point : S -> K) : Prop :=
  forall p : q1068976_polynomial S k,
    q1068976_ideal_mem I p ->
    @q1068976_evaluate S k K FS Fk FK A point p =
    q1068976_zero FK.

Definition q1068976_vanishing_ideal_member
    {S k K : Type}
    (FS : q1068976_finite_index S)
    (Fk : q1068976_field k)
    (FK : q1068976_field K)
    (A : q1068976_field_algebra Fk FK)
    (I : q1068976_ideal FS Fk)
    (p : q1068976_polynomial S k) : Prop :=
  forall point : S -> K,
    @q1068976_zero_locus S k K FS Fk FK A I point ->
    @q1068976_evaluate S k K FS Fk FK A point p =
    q1068976_zero FK.

Definition q1068976_radical_member
    {S k : Type}
    (FS : q1068976_finite_index S)
    (Fk : q1068976_field k)
    (I : q1068976_ideal FS Fk)
    (p : q1068976_polynomial S k) : Prop :=
  exists exponent : nat,
    q1068976_ideal_mem I
      (q1068976_polynomial_pow Fk p (Datatypes.S exponent)).

Theorem MvPolynomial_vanishingIdeal_zeroLocus_eq_radical :
  forall (k K : Type)
         (Fk : q1068976_field k)
         (FK : q1068976_field K)
         (A : q1068976_field_algebra Fk FK),
    q1068976_is_algebraically_closed FK ->
    forall (S : Type)
           (FS : q1068976_finite_index S)
           (I : q1068976_ideal FS Fk)
           (p : q1068976_polynomial S k),
      @q1068976_vanishing_ideal_member S k K FS Fk FK A I p <->
      @q1068976_radical_member S k FS Fk I p.
Admitted.
