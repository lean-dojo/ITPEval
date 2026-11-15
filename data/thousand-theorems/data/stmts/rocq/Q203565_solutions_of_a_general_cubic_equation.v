(*
  Statement-only formalization of Thousand Theorems corpus artifact Q203565
  (thousand-theorems__rocq__Q203565), "Solutions of a general cubic equation":
  over a field where 2 and 3 are invertible and a primitive cube root of unity
  exists, the roots of a cubic with nonzero Cardano parameter are exactly the
  three stated Cardano expressions. This file contains no proof.
*)

From Stdlib Require Import Arith.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q203565_field (K : Type) : Type := {
  q203565_zero : K;
  q203565_one : K;
  q203565_add : K -> K -> K;
  q203565_mul : K -> K -> K;
  q203565_neg : K -> K;
  q203565_inv : K -> K;
  q203565_add_assoc :
    forall x y z : K,
      q203565_add x (q203565_add y z) =
      q203565_add (q203565_add x y) z;
  q203565_add_comm :
    forall x y : K,
      q203565_add x y = q203565_add y x;
  q203565_add_zero :
    forall x : K,
      q203565_add x q203565_zero = x;
  q203565_add_neg :
    forall x : K,
      q203565_add x (q203565_neg x) = q203565_zero;
  q203565_mul_assoc :
    forall x y z : K,
      q203565_mul x (q203565_mul y z) =
      q203565_mul (q203565_mul x y) z;
  q203565_mul_comm :
    forall x y : K,
      q203565_mul x y = q203565_mul y x;
  q203565_mul_one :
    forall x : K,
      q203565_mul x q203565_one = x;
  q203565_left_distrib :
    forall x y z : K,
      q203565_mul x (q203565_add y z) =
      q203565_add
        (q203565_mul x y)
        (q203565_mul x z);
  q203565_inv_zero :
    q203565_inv q203565_zero = q203565_zero;
  q203565_mul_inv :
    forall x : K,
      x <> q203565_zero ->
      q203565_mul x (q203565_inv x) = q203565_one;
  q203565_nontrivial :
    q203565_zero <> q203565_one
}.

Arguments q203565_zero {K} _.
Arguments q203565_one {K} _.
Arguments q203565_add {K} _ _ _.
Arguments q203565_mul {K} _ _ _.
Arguments q203565_neg {K} _ _.
Arguments q203565_inv {K} _ _.

Definition q203565_sub
    {K : Type} (F : q203565_field K) (x y : K) : K :=
  q203565_add F x (q203565_neg F y).

Definition q203565_div
    {K : Type} (F : q203565_field K) (x y : K) : K :=
  q203565_mul F x (q203565_inv F y).

Fixpoint q203565_pow
    {K : Type} (F : q203565_field K) (x : K) (n : nat) : K :=
  match n with
  | O => q203565_one F
  | S m => q203565_mul F x (q203565_pow F x m)
  end.

Fixpoint q203565_of_nat
    {K : Type} (F : q203565_field K) (n : nat) : K :=
  match n with
  | O => q203565_zero F
  | S m => q203565_add F (q203565_of_nat F m) (q203565_one F)
  end.

Definition q203565_invertible
    {K : Type} (F : q203565_field K) (x : K) : Prop :=
  exists y : K,
    q203565_mul F x y = q203565_one F.

Definition q203565_is_primitive_root
    {K : Type} (F : q203565_field K) (omega : K) (n : nat) : Prop :=
  q203565_pow F omega n = q203565_one F /\
  forall k : nat,
    q203565_pow F omega k = q203565_one F <->
    exists m : nat, k = n * m.

Module Theorems100.

Theorem cubic_eq_zero_iff :
  forall
    (K : Type)
    (F : q203565_field K)
    (a b c d omega p q r s t x : K),
    q203565_invertible F (q203565_of_nat F 2) ->
    q203565_invertible F (q203565_of_nat F 3) ->
    a <> q203565_zero F ->
    q203565_is_primitive_root F omega 3 ->
    p =
      q203565_div F
        (q203565_sub F
          (q203565_mul F
            (q203565_mul F (q203565_of_nat F 3) a) c)
          (q203565_pow F b 2))
        (q203565_mul F
          (q203565_of_nat F 9)
          (q203565_pow F a 2)) ->
    p <> q203565_zero F ->
    q =
      q203565_div F
        (q203565_sub F
          (q203565_sub F
            (q203565_mul F
              (q203565_mul F
                (q203565_mul F (q203565_of_nat F 9) a) b)
              c)
            (q203565_mul F
              (q203565_of_nat F 2)
              (q203565_pow F b 3)))
          (q203565_mul F
            (q203565_mul F
              (q203565_of_nat F 27)
              (q203565_pow F a 2))
            d))
        (q203565_mul F
          (q203565_of_nat F 54)
          (q203565_pow F a 3)) ->
    q203565_pow F r 2 =
      q203565_add F
        (q203565_pow F q 2)
        (q203565_pow F p 3) ->
    q203565_pow F s 3 = q203565_add F q r ->
    q203565_mul F t s = p ->
    (q203565_add F
      (q203565_add F
        (q203565_add F
          (q203565_mul F a (q203565_pow F x 3))
          (q203565_mul F b (q203565_pow F x 2)))
        (q203565_mul F c x))
      d = q203565_zero F
     <->
     x =
       q203565_sub F
         (q203565_sub F s t)
         (q203565_div F b
           (q203565_mul F (q203565_of_nat F 3) a))
     \/
     x =
       q203565_sub F
         (q203565_sub F
           (q203565_mul F s omega)
           (q203565_mul F t (q203565_pow F omega 2)))
         (q203565_div F b
           (q203565_mul F (q203565_of_nat F 3) a))
     \/
     x =
       q203565_sub F
         (q203565_sub F
           (q203565_mul F s (q203565_pow F omega 2))
           (q203565_mul F t omega))
         (q203565_div F b
           (q203565_mul F (q203565_of_nat F 3) a))).
Admitted.

End Theorems100.
