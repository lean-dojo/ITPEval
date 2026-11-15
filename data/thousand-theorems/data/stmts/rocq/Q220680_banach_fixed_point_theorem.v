(*
  Statement-only formalization of Thousand Theorems corpus artifact Q220680
  (thousand-theorems__rocq__Q220680), "Banach fixed-point theorem": a
  contraction on a complete extended metric space, started from a point with
  finite initial displacement, has a fixed point; its iterates converge to
  that point and satisfy the geometric error estimate. This file contains no
  proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Inductive q220680_ennreal : Type :=
| q220680_ennreal_finite :
    forall value : R, 0 <= value -> q220680_ennreal
| q220680_ennreal_infinity : q220680_ennreal.

Arguments q220680_ennreal_finite value nonnegative : clear implicits.

Definition q220680_ennreal_zero : q220680_ennreal :=
  q220680_ennreal_finite 0 (Rle_refl 0).

Definition q220680_ennreal_eq
    (x y : q220680_ennreal) : Prop :=
  match x, y with
  | q220680_ennreal_finite a _,
    q220680_ennreal_finite b _ => a = b
  | q220680_ennreal_infinity,
    q220680_ennreal_infinity => True
  | _, _ => False
  end.

Definition q220680_ennreal_le
    (x y : q220680_ennreal) : Prop :=
  match x, y with
  | q220680_ennreal_finite a _,
    q220680_ennreal_finite b _ => a <= b
  | q220680_ennreal_finite _ _,
    q220680_ennreal_infinity => True
  | q220680_ennreal_infinity,
    q220680_ennreal_finite _ _ => False
  | q220680_ennreal_infinity,
    q220680_ennreal_infinity => True
  end.

Definition q220680_ennreal_add
    (x y : q220680_ennreal) : q220680_ennreal :=
  match x, y with
  | q220680_ennreal_finite a ha,
    q220680_ennreal_finite b hb =>
      q220680_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q220680_ennreal_infinity
  end.

Definition q220680_ennreal_scale
    (coefficient : R)
    (x : q220680_ennreal) : q220680_ennreal :=
  match x with
  | q220680_ennreal_finite value _ =>
      q220680_ennreal_finite
        (Rmax (coefficient * value) 0)
        (Rmax_r (coefficient * value) 0)
  | q220680_ennreal_infinity =>
      if Req_EM_T coefficient 0
      then q220680_ennreal_zero
      else q220680_ennreal_infinity
  end.

Definition q220680_ennreal_lt_real
    (x : q220680_ennreal) (bound : R) : Prop :=
  match x with
  | q220680_ennreal_finite value _ => value < bound
  | q220680_ennreal_infinity => False
  end.

Definition q220680_ennreal_is_finite
    (x : q220680_ennreal) : Prop :=
  match x with
  | q220680_ennreal_finite _ _ => True
  | q220680_ennreal_infinity => False
  end.

Record q220680_nnreal : Type := {
  q220680_nnreal_value : R;
  q220680_nnreal_nonnegative : 0 <= q220680_nnreal_value
}.

Record q220680_emetric_space (Alpha : Type) : Type := {
  q220680_edist : Alpha -> Alpha -> q220680_ennreal;
  q220680_edist_self :
    forall x : Alpha,
      q220680_ennreal_eq
        (q220680_edist x x) q220680_ennreal_zero;
  q220680_edist_comm :
    forall x y : Alpha,
      q220680_ennreal_eq
        (q220680_edist x y) (q220680_edist y x);
  q220680_edist_triangle :
    forall x y z : Alpha,
      q220680_ennreal_le
        (q220680_edist x z)
        (q220680_ennreal_add
          (q220680_edist x y) (q220680_edist y z));
  q220680_edist_eq_zero :
    forall x y : Alpha,
      q220680_ennreal_eq
        (q220680_edist x y) q220680_ennreal_zero <->
      x = y
}.

Arguments q220680_edist {Alpha} _ _ _.

Definition q220680_sequence_converges
    {Alpha : Type}
    (E : q220680_emetric_space Alpha)
    (u : nat -> Alpha) (limit : Alpha) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q220680_ennreal_lt_real
          (q220680_edist E (u n) limit) epsilon.

Definition q220680_sequence_cauchy
    {Alpha : Type}
    (E : q220680_emetric_space Alpha)
    (u : nat -> Alpha) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall m n : nat,
        (N <= m)%nat ->
        (N <= n)%nat ->
        q220680_ennreal_lt_real
          (q220680_edist E (u m) (u n)) epsilon.

Definition q220680_complete
    {Alpha : Type}
    (E : q220680_emetric_space Alpha) : Prop :=
  forall u : nat -> Alpha,
    q220680_sequence_cauchy E u ->
    exists limit : Alpha,
      q220680_sequence_converges E u limit.

Fixpoint q220680_iterate
    {Alpha : Type}
    (f : Alpha -> Alpha) (n : nat) (x : Alpha) : Alpha :=
  match n with
  | O => x
  | S k => f (q220680_iterate f k x)
  end.

Definition q220680_contracting_with
    {Alpha : Type}
    (E : q220680_emetric_space Alpha)
    (K : q220680_nnreal)
    (f : Alpha -> Alpha) : Prop :=
  q220680_nnreal_value K < 1 /\
  forall x y : Alpha,
    q220680_ennreal_le
      (q220680_edist E (f x) (f y))
      (q220680_ennreal_scale
        (q220680_nnreal_value K)
        (q220680_edist E x y)).

Theorem ContractingWith_exists_fixedPoint :
  forall (Alpha : Type)
         (E : q220680_emetric_space Alpha)
         (K : q220680_nnreal)
         (f : Alpha -> Alpha)
         (x : Alpha),
    q220680_complete E ->
    q220680_contracting_with E K f ->
    q220680_ennreal_is_finite
      (q220680_edist E x (f x)) ->
    exists y : Alpha,
      f y = y /\
      q220680_sequence_converges E
        (fun n : nat => q220680_iterate f n x) y /\
      forall n : nat,
        q220680_ennreal_le
          (q220680_edist E (q220680_iterate f n x) y)
          (q220680_ennreal_scale
            (((q220680_nnreal_value K) ^ n) /
              (1 - q220680_nnreal_value K))
            (q220680_edist E x (f x))).
Admitted.
