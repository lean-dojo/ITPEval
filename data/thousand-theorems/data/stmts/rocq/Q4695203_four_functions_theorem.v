(*
  Statement-only formalization of Thousand Theorems corpus artifact Q4695203
  (thousand-theorems__rocq__Q4695203), "Four functions theorem": a pointwise
  meet-join product inequality for four nonnegative functions on a
  distributive lattice implies the corresponding inequality for sums over
  two finite families and their pairwise meets and joins. This file contains
  no proof.
*)

From Stdlib Require Import List.

Import ListNotations.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q4695203_distributive_lattice (A : Type) : Type := {
  q4695203_le : A -> A -> Prop;
  q4695203_meet : A -> A -> A;
  q4695203_join : A -> A -> A;
  q4695203_le_refl :
    forall x : A, q4695203_le x x;
  q4695203_le_trans :
    forall x y z : A,
      q4695203_le x y ->
      q4695203_le y z ->
      q4695203_le x z;
  q4695203_le_antisym :
    forall x y : A,
      q4695203_le x y ->
      q4695203_le y x ->
      x = y;
  q4695203_meet_le_left :
    forall x y : A,
      q4695203_le (q4695203_meet x y) x;
  q4695203_meet_le_right :
    forall x y : A,
      q4695203_le (q4695203_meet x y) y;
  q4695203_le_meet :
    forall x y z : A,
      q4695203_le z x ->
      q4695203_le z y ->
      q4695203_le z (q4695203_meet x y);
  q4695203_le_join_left :
    forall x y : A,
      q4695203_le x (q4695203_join x y);
  q4695203_le_join_right :
    forall x y : A,
      q4695203_le y (q4695203_join x y);
  q4695203_join_le :
    forall x y z : A,
      q4695203_le x z ->
      q4695203_le y z ->
      q4695203_le (q4695203_join x y) z;
  q4695203_meet_join_distrib_left :
    forall x y z : A,
      q4695203_meet x (q4695203_join y z) =
      q4695203_join
        (q4695203_meet x y)
        (q4695203_meet x z)
}.

Arguments q4695203_le {A} _ _ _.
Arguments q4695203_meet {A} _ _ _.
Arguments q4695203_join {A} _ _ _.

Record q4695203_ordered_comm_semiring (B : Type) : Type := {
  q4695203_zero : B;
  q4695203_one : B;
  q4695203_add : B -> B -> B;
  q4695203_mul : B -> B -> B;
  q4695203_ord_le : B -> B -> Prop;
  q4695203_ord_lt : B -> B -> Prop;
  q4695203_add_assoc :
    forall x y z : B,
      q4695203_add x (q4695203_add y z) =
      q4695203_add (q4695203_add x y) z;
  q4695203_add_comm :
    forall x y : B,
      q4695203_add x y = q4695203_add y x;
  q4695203_zero_add :
    forall x : B,
      q4695203_add q4695203_zero x = x;
  q4695203_add_zero :
    forall x : B,
      q4695203_add x q4695203_zero = x;
  q4695203_mul_assoc :
    forall x y z : B,
      q4695203_mul x (q4695203_mul y z) =
      q4695203_mul (q4695203_mul x y) z;
  q4695203_mul_comm :
    forall x y : B,
      q4695203_mul x y = q4695203_mul y x;
  q4695203_one_mul :
    forall x : B,
      q4695203_mul q4695203_one x = x;
  q4695203_mul_one :
    forall x : B,
      q4695203_mul x q4695203_one = x;
  q4695203_mul_add :
    forall x y z : B,
      q4695203_mul x (q4695203_add y z) =
      q4695203_add
        (q4695203_mul x y)
        (q4695203_mul x z);
  q4695203_add_mul :
    forall x y z : B,
      q4695203_mul (q4695203_add x y) z =
      q4695203_add
        (q4695203_mul x z)
        (q4695203_mul y z);
  q4695203_zero_mul :
    forall x : B,
      q4695203_mul q4695203_zero x = q4695203_zero;
  q4695203_mul_zero :
    forall x : B,
      q4695203_mul x q4695203_zero = q4695203_zero;
  q4695203_ord_le_refl :
    forall x : B, q4695203_ord_le x x;
  q4695203_ord_le_trans :
    forall x y z : B,
      q4695203_ord_le x y ->
      q4695203_ord_le y z ->
      q4695203_ord_le x z;
  q4695203_ord_le_antisym :
    forall x y : B,
      q4695203_ord_le x y ->
      q4695203_ord_le y x ->
      x = y;
  q4695203_ord_le_total :
    forall x y : B,
      q4695203_ord_le x y \/ q4695203_ord_le y x;
  q4695203_ord_le_dec :
    forall x y : B,
      {q4695203_ord_le x y} + {~ q4695203_ord_le x y};
  q4695203_ord_lt_iff :
    forall x y : B,
      q4695203_ord_lt x y <->
      q4695203_ord_le x y /\ x <> y;
  q4695203_ord_lt_dec :
    forall x y : B,
      {q4695203_ord_lt x y} + {~ q4695203_ord_lt x y};
  q4695203_nontrivial :
    exists x y : B, x <> y;
  q4695203_zero_le_one :
    q4695203_ord_le q4695203_zero q4695203_one;
  q4695203_add_le_add_left_iff :
    forall x y z : B,
      q4695203_ord_le
        (q4695203_add z x)
        (q4695203_add z y) <->
      q4695203_ord_le x y;
  q4695203_mul_lt_mul_of_pos_left :
    forall x y z : B,
      q4695203_ord_lt q4695203_zero x ->
      q4695203_ord_lt y z ->
      q4695203_ord_lt
        (q4695203_mul x y)
        (q4695203_mul x z);
  q4695203_mul_lt_mul_of_pos_right :
    forall x y z : B,
      q4695203_ord_lt q4695203_zero z ->
      q4695203_ord_lt x y ->
      q4695203_ord_lt
        (q4695203_mul x z)
        (q4695203_mul y z);
  q4695203_exists_add_of_le :
    forall x y : B,
      q4695203_ord_le x y ->
      exists z : B, y = q4695203_add x z
}.

Arguments q4695203_zero {B} _.
Arguments q4695203_one {B} _.
Arguments q4695203_add {B} _ _ _.
Arguments q4695203_mul {B} _ _ _.
Arguments q4695203_ord_le {B} _ _ _.
Arguments q4695203_ord_lt {B} _ _ _.

Fixpoint q4695203_sum
    {A B : Type}
    (R : q4695203_ordered_comm_semiring B)
    (f : A -> B)
    (xs : list A) : B :=
  match xs with
  | [] => q4695203_zero R
  | x :: xs' =>
      q4695203_add R (f x) (q4695203_sum R f xs')
  end.

Fixpoint q4695203_image2_raw
    {A : Type}
    (op : A -> A -> A)
    (xs ys : list A) : list A :=
  match xs with
  | [] => []
  | x :: xs' =>
      map (op x) ys ++ q4695203_image2_raw op xs' ys
  end.

Fixpoint q4695203_dedup
    {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: xs' =>
      if in_dec eq_dec x xs'
      then q4695203_dedup eq_dec xs'
      else x :: q4695203_dedup eq_dec xs'
  end.

Definition q4695203_image2
    {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (op : A -> A -> A)
    (xs ys : list A) : list A :=
  q4695203_dedup eq_dec
    (q4695203_image2_raw op xs ys).

Theorem four_functions_theorem :
  forall
    (A B : Type)
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (L : q4695203_distributive_lattice A)
    (R : q4695203_ordered_comm_semiring B)
    (f1 f2 f3 f4 : A -> B),
    (forall a : A,
      q4695203_ord_le R (q4695203_zero R) (f1 a)) ->
    (forall a : A,
      q4695203_ord_le R (q4695203_zero R) (f2 a)) ->
    (forall a : A,
      q4695203_ord_le R (q4695203_zero R) (f3 a)) ->
    (forall a : A,
      q4695203_ord_le R (q4695203_zero R) (f4 a)) ->
    (forall a b : A,
      q4695203_ord_le R
        (q4695203_mul R (f1 a) (f2 b))
        (q4695203_mul R
          (f3 (q4695203_meet L a b))
          (f4 (q4695203_join L a b)))) ->
    forall s t : list A,
      NoDup s ->
      NoDup t ->
      q4695203_ord_le R
        (q4695203_mul R
          (q4695203_sum R f1 s)
          (q4695203_sum R f2 t))
        (q4695203_mul R
          (q4695203_sum R f3
            (q4695203_image2 eq_dec
              (q4695203_meet L) s t))
          (q4695203_sum R f4
            (q4695203_image2 eq_dec
              (q4695203_join L) s t))).
Admitted.
