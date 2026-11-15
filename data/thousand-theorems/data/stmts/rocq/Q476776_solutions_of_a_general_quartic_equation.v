(*
  Statement-only formalization of Thousand Theorems corpus artifact Q476776
  (thousand-theorems__rocq__Q476776), "Solutions of a general quartic equation":
  over a field where 2 is invertible, the roots of a quartic with nonzero
  depressed-quartic linear coefficient are exactly the four stated expressions
  determined by a root of its cubic resolvent. This file contains no proof.
*)

From Stdlib Require Import Arith.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q476776_field (K : Type) : Type := {
  q476776_zero : K;
  q476776_one : K;
  q476776_add : K -> K -> K;
  q476776_mul : K -> K -> K;
  q476776_neg : K -> K;
  q476776_inv : K -> K;
  q476776_add_assoc :
    forall x y z : K,
      q476776_add x (q476776_add y z) =
      q476776_add (q476776_add x y) z;
  q476776_add_comm :
    forall x y : K,
      q476776_add x y = q476776_add y x;
  q476776_add_zero :
    forall x : K,
      q476776_add x q476776_zero = x;
  q476776_add_neg :
    forall x : K,
      q476776_add x (q476776_neg x) = q476776_zero;
  q476776_mul_assoc :
    forall x y z : K,
      q476776_mul x (q476776_mul y z) =
      q476776_mul (q476776_mul x y) z;
  q476776_mul_comm :
    forall x y : K,
      q476776_mul x y = q476776_mul y x;
  q476776_mul_one :
    forall x : K,
      q476776_mul x q476776_one = x;
  q476776_left_distrib :
    forall x y z : K,
      q476776_mul x (q476776_add y z) =
      q476776_add
        (q476776_mul x y)
        (q476776_mul x z);
  q476776_inv_zero :
    q476776_inv q476776_zero = q476776_zero;
  q476776_mul_inv :
    forall x : K,
      x <> q476776_zero ->
      q476776_mul x (q476776_inv x) = q476776_one;
  q476776_nontrivial :
    q476776_zero <> q476776_one
}.

Arguments q476776_zero {K} _.
Arguments q476776_one {K} _.
Arguments q476776_add {K} _ _ _.
Arguments q476776_mul {K} _ _ _.
Arguments q476776_neg {K} _ _.
Arguments q476776_inv {K} _ _.

Definition q476776_sub
    {K : Type} (F : q476776_field K) (x y : K) : K :=
  q476776_add F x (q476776_neg F y).

Definition q476776_div
    {K : Type} (F : q476776_field K) (x y : K) : K :=
  q476776_mul F x (q476776_inv F y).

Fixpoint q476776_pow
    {K : Type} (F : q476776_field K) (x : K) (n : nat) : K :=
  match n with
  | O => q476776_one F
  | S m => q476776_mul F x (q476776_pow F x m)
  end.

Fixpoint q476776_of_nat
    {K : Type} (F : q476776_field K) (n : nat) : K :=
  match n with
  | O => q476776_zero F
  | S m => q476776_add F (q476776_of_nat F m) (q476776_one F)
  end.

Definition q476776_invertible
    {K : Type} (F : q476776_field K) (x : K) : Prop :=
  exists y : K,
    q476776_mul F x y = q476776_one F.

Module Theorems100.

Theorem quartic_eq_zero_iff :
  forall
    (K : Type)
    (F : q476776_field K)
    (a b c d e p q r s u v w x : K),
    q476776_invertible F (q476776_of_nat F 2) ->
    a <> q476776_zero F ->
    p =
      q476776_div F
        (q476776_sub F
          (q476776_mul F
            (q476776_mul F (q476776_of_nat F 8) a) c)
          (q476776_mul F
            (q476776_of_nat F 3)
            (q476776_pow F b 2)))
        (q476776_mul F
          (q476776_of_nat F 8)
          (q476776_pow F a 2)) ->
    q =
      q476776_div F
        (q476776_add F
          (q476776_sub F
            (q476776_pow F b 3)
            (q476776_mul F
              (q476776_mul F
                (q476776_mul F (q476776_of_nat F 4) a) b)
              c))
          (q476776_mul F
            (q476776_mul F
              (q476776_of_nat F 8)
              (q476776_pow F a 2))
            d))
        (q476776_mul F
          (q476776_of_nat F 8)
          (q476776_pow F a 3)) ->
    q <> q476776_zero F ->
    r =
      q476776_div F
        (q476776_sub F
          (q476776_sub F
            (q476776_add F
              (q476776_mul F
                (q476776_mul F
                  (q476776_mul F
                    (q476776_of_nat F 16)
                    a)
                  (q476776_pow F b 2))
                c)
              (q476776_mul F
                (q476776_mul F
                  (q476776_of_nat F 256)
                  (q476776_pow F a 3))
                e))
            (q476776_mul F
              (q476776_of_nat F 3)
              (q476776_pow F b 4)))
          (q476776_mul F
            (q476776_mul F
              (q476776_mul F
                (q476776_of_nat F 64)
                (q476776_pow F a 2))
              b)
            d))
        (q476776_mul F
          (q476776_of_nat F 256)
          (q476776_pow F a 4)) ->
    q476776_sub F
      (q476776_add F
        (q476776_sub F
          (q476776_sub F
            (q476776_pow F u 3)
            (q476776_mul F p (q476776_pow F u 2)))
          (q476776_mul F
            (q476776_mul F (q476776_of_nat F 4) r)
            u))
        (q476776_mul F
          (q476776_mul F (q476776_of_nat F 4) p)
          r))
      (q476776_pow F q 2) =
      q476776_zero F ->
    q476776_pow F s 2 = q476776_sub F u p ->
    q476776_pow F v 2 =
      q476776_sub F
        (q476776_mul F
          (q476776_of_nat F 4)
          (q476776_pow F s 2))
        (q476776_mul F
          (q476776_of_nat F 8)
          (q476776_sub F u (q476776_div F q s))) ->
    q476776_pow F w 2 =
      q476776_sub F
        (q476776_mul F
          (q476776_of_nat F 4)
          (q476776_pow F s 2))
        (q476776_mul F
          (q476776_of_nat F 8)
          (q476776_add F u (q476776_div F q s))) ->
    (q476776_add F
      (q476776_add F
        (q476776_add F
          (q476776_add F
            (q476776_mul F a (q476776_pow F x 4))
            (q476776_mul F b (q476776_pow F x 3)))
          (q476776_mul F c (q476776_pow F x 2)))
        (q476776_mul F d x))
      e = q476776_zero F
     <->
     x =
       q476776_sub F
         (q476776_div F
           (q476776_sub F
             (q476776_mul F
               (q476776_neg F (q476776_of_nat F 2))
               s)
             v)
           (q476776_of_nat F 4))
         (q476776_div F b
           (q476776_mul F (q476776_of_nat F 4) a))
     \/
     x =
       q476776_sub F
         (q476776_div F
           (q476776_add F
             (q476776_mul F
               (q476776_neg F (q476776_of_nat F 2))
               s)
             v)
           (q476776_of_nat F 4))
         (q476776_div F b
           (q476776_mul F (q476776_of_nat F 4) a))
     \/
     x =
       q476776_sub F
         (q476776_div F
           (q476776_sub F
             (q476776_mul F (q476776_of_nat F 2) s)
             w)
           (q476776_of_nat F 4))
         (q476776_div F b
           (q476776_mul F (q476776_of_nat F 4) a))
     \/
     x =
       q476776_sub F
         (q476776_div F
           (q476776_add F
             (q476776_mul F (q476776_of_nat F 2) s)
             w)
           (q476776_of_nat F 4))
         (q476776_div F b
           (q476776_mul F (q476776_of_nat F 4) a))).
Admitted.

End Theorems100.
