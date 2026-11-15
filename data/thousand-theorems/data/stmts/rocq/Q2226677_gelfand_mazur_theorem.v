(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2226677
  (thousand-theorems__rocq__Q2226677), "Gelfand-Mazur theorem": the natural
  complex algebra map into a complete normed complex algebra in which every
  nonzero element is a unit is an algebra equivalence. This file contains no
  proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q2226677_complex : Type := (R * R)%type.

Definition q2226677_czero : q2226677_complex := (0, 0).
Definition q2226677_cone : q2226677_complex := (1, 0).

Definition q2226677_cadd
    (z w : q2226677_complex) : q2226677_complex :=
  (fst z + fst w, snd z + snd w).

Definition q2226677_cmul
    (z w : q2226677_complex) : q2226677_complex :=
  (fst z * fst w - snd z * snd w,
   fst z * snd w + snd z * fst w).

Definition q2226677_cmodulus
    (z : q2226677_complex) : R :=
  sqrt (fst z * fst z + snd z * snd z).

Record q2226677_normed_complex_algebra (A : Type) : Type := {
  q2226677_zero : A;
  q2226677_one : A;
  q2226677_add : A -> A -> A;
  q2226677_mul : A -> A -> A;
  q2226677_neg : A -> A;
  q2226677_algebra_map : q2226677_complex -> A;
  q2226677_norm : A -> R;

  q2226677_add_assoc :
    forall x y z : A,
      q2226677_add x (q2226677_add y z) =
      q2226677_add (q2226677_add x y) z;
  q2226677_add_comm :
    forall x y : A,
      q2226677_add x y = q2226677_add y x;
  q2226677_add_zero :
    forall x : A,
      q2226677_add x q2226677_zero = x;
  q2226677_add_neg :
    forall x : A,
      q2226677_add x (q2226677_neg x) = q2226677_zero;

  q2226677_mul_assoc :
    forall x y z : A,
      q2226677_mul x (q2226677_mul y z) =
      q2226677_mul (q2226677_mul x y) z;
  q2226677_mul_one_left :
    forall x : A,
      q2226677_mul q2226677_one x = x;
  q2226677_mul_one_right :
    forall x : A,
      q2226677_mul x q2226677_one = x;
  q2226677_left_distrib :
    forall x y z : A,
      q2226677_mul x (q2226677_add y z) =
      q2226677_add
        (q2226677_mul x y) (q2226677_mul x z);
  q2226677_right_distrib :
    forall x y z : A,
      q2226677_mul (q2226677_add x y) z =
      q2226677_add
        (q2226677_mul x z) (q2226677_mul y z);

  q2226677_algebra_map_zero :
    q2226677_algebra_map q2226677_czero = q2226677_zero;
  q2226677_algebra_map_one :
    q2226677_algebra_map q2226677_cone = q2226677_one;
  q2226677_algebra_map_add :
    forall z w : q2226677_complex,
      q2226677_algebra_map (q2226677_cadd z w) =
      q2226677_add
        (q2226677_algebra_map z) (q2226677_algebra_map w);
  q2226677_algebra_map_mul :
    forall z w : q2226677_complex,
      q2226677_algebra_map (q2226677_cmul z w) =
      q2226677_mul
        (q2226677_algebra_map z) (q2226677_algebra_map w);
  q2226677_algebra_map_central :
    forall (z : q2226677_complex) (x : A),
      q2226677_mul (q2226677_algebra_map z) x =
      q2226677_mul x (q2226677_algebra_map z);

  q2226677_norm_nonnegative :
    forall x : A,
      0 <= q2226677_norm x;
  q2226677_norm_eq_zero :
    forall x : A,
      q2226677_norm x = 0 <-> x = q2226677_zero;
  q2226677_norm_neg :
    forall x : A,
      q2226677_norm (q2226677_neg x) = q2226677_norm x;
  q2226677_norm_add_le :
    forall x y : A,
      q2226677_norm (q2226677_add x y) <=
      q2226677_norm x + q2226677_norm y;
  q2226677_norm_mul_le :
    forall x y : A,
      q2226677_norm (q2226677_mul x y) <=
      q2226677_norm x * q2226677_norm y;
  q2226677_norm_smul :
    forall (z : q2226677_complex) (x : A),
      q2226677_norm
        (q2226677_mul (q2226677_algebra_map z) x) =
      q2226677_cmodulus z * q2226677_norm x
}.

Arguments q2226677_zero {A} _.
Arguments q2226677_one {A} _.
Arguments q2226677_add {A} _ _ _.
Arguments q2226677_mul {A} _ _ _.
Arguments q2226677_neg {A} _ _.
Arguments q2226677_algebra_map {A} _ _.
Arguments q2226677_norm {A} _ _.

Definition q2226677_sub
    {A : Type}
    (B : q2226677_normed_complex_algebra A)
    (x y : A) : A :=
  q2226677_add B x (q2226677_neg B y).

Definition q2226677_dist
    {A : Type}
    (B : q2226677_normed_complex_algebra A)
    (x y : A) : R :=
  q2226677_norm B (q2226677_sub B x y).

Definition q2226677_sequence_converges
    {A : Type}
    (B : q2226677_normed_complex_algebra A)
    (u : nat -> A) (limit : A) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q2226677_dist B (u n) limit < epsilon.

Definition q2226677_sequence_cauchy
    {A : Type}
    (B : q2226677_normed_complex_algebra A)
    (u : nat -> A) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall m n : nat,
        (N <= m)%nat ->
        (N <= n)%nat ->
        q2226677_dist B (u m) (u n) < epsilon.

Definition q2226677_complete
    {A : Type}
    (B : q2226677_normed_complex_algebra A) : Prop :=
  forall u : nat -> A,
    q2226677_sequence_cauchy B u ->
    exists limit : A,
      q2226677_sequence_converges B u limit.

Definition q2226677_is_unit
    {A : Type}
    (B : q2226677_normed_complex_algebra A)
    (x : A) : Prop :=
  exists inverse : A,
    q2226677_mul B x inverse = q2226677_one B /\
    q2226677_mul B inverse x = q2226677_one B.

Theorem NormedRing_algEquivComplexOfComplete :
  forall (A : Type)
         (B : q2226677_normed_complex_algebra A),
    q2226677_complete B ->
    (forall a : A,
      q2226677_is_unit B a <-> a <> q2226677_zero B) ->
    exists inverse : A -> q2226677_complex,
      (forall z : q2226677_complex,
        inverse (q2226677_algebra_map B z) = z) /\
      (forall a : A,
        q2226677_algebra_map B (inverse a) = a).
Admitted.
