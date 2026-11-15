(*
  Statement-only formalization of Thousand Theorems corpus artifact Q943246
  (thousand-theorems__rocq__Q943246), "Wedderburn's little theorem": every
  finite division ring has commutative multiplication and hence is a field.
  This file contains no proof.
*)

From Stdlib Require Import List.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q943246_division_ring (D : Type) : Type := {
  q943246_zero : D;
  q943246_one : D;
  q943246_add : D -> D -> D;
  q943246_mul : D -> D -> D;
  q943246_neg : D -> D;
  q943246_inv : D -> D;
  q943246_add_assoc :
    forall x y z : D,
      q943246_add x (q943246_add y z) =
      q943246_add (q943246_add x y) z;
  q943246_add_comm :
    forall x y : D,
      q943246_add x y = q943246_add y x;
  q943246_zero_add :
    forall x : D, q943246_add q943246_zero x = x;
  q943246_add_zero :
    forall x : D, q943246_add x q943246_zero = x;
  q943246_add_neg :
    forall x : D,
      q943246_add x (q943246_neg x) = q943246_zero;
  q943246_neg_add :
    forall x : D,
      q943246_add (q943246_neg x) x = q943246_zero;
  q943246_mul_assoc :
    forall x y z : D,
      q943246_mul x (q943246_mul y z) =
      q943246_mul (q943246_mul x y) z;
  q943246_one_mul :
    forall x : D, q943246_mul q943246_one x = x;
  q943246_mul_one :
    forall x : D, q943246_mul x q943246_one = x;
  q943246_mul_add :
    forall x y z : D,
      q943246_mul x (q943246_add y z) =
      q943246_add
        (q943246_mul x y)
        (q943246_mul x z);
  q943246_add_mul :
    forall x y z : D,
      q943246_mul (q943246_add x y) z =
      q943246_add
        (q943246_mul x z)
        (q943246_mul y z);
  q943246_zero_mul :
    forall x : D,
      q943246_mul q943246_zero x = q943246_zero;
  q943246_mul_zero :
    forall x : D,
      q943246_mul x q943246_zero = q943246_zero;
  q943246_zero_ne_one :
    q943246_zero <> q943246_one;
  q943246_inv_zero :
    q943246_inv q943246_zero = q943246_zero;
  q943246_mul_inv :
    forall x : D,
      x <> q943246_zero ->
      q943246_mul x (q943246_inv x) = q943246_one;
  q943246_inv_mul :
    forall x : D,
      x <> q943246_zero ->
      q943246_mul (q943246_inv x) x = q943246_one
}.

Arguments q943246_zero {D} _.
Arguments q943246_one {D} _.
Arguments q943246_add {D} _ _ _.
Arguments q943246_mul {D} _ _ _.
Arguments q943246_neg {D} _ _.
Arguments q943246_inv {D} _ _.

Definition q943246_finite (D : Type) : Prop :=
  exists elements : list D,
    forall x : D, List.In x elements.

Definition q943246_is_field
    {D : Type}
    (DR : q943246_division_ring D) : Prop :=
  forall x y : D,
    q943246_mul DR x y = q943246_mul DR y x.

Theorem littleWedderburn :
  forall (D : Type) (DR : q943246_division_ring D),
    q943246_finite D ->
    q943246_is_field DR.
Admitted.
