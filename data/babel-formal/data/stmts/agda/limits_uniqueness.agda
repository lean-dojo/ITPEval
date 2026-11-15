-- Statement-only formalization of the Babel-formal topic limits_uniqueness. This file contains
-- no proof.

module limits_uniqueness where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ)

record AbsField (R N : Set) : Set₁ where
  field
    zero : R
    one  : R
    add  : R → R → R
    mul  : R → R → R
    opp  : R → R
    abs  : R → R
    le   : R → R → Set
    lt   : R → R → Set

    nat-le  : N → N → Set
    nat-max : N → N → N
    nat-le-max-left  : (x y : N) → nat-le x (nat-max x y)
    nat-le-max-right : (x y : N) → nat-le y (nat-max x y)

    add-comm  : (x y : R) → add x y ≡ add y x
    add-assoc : (x y z : R) → add (add x y) z ≡ add x (add y z)
    add-zero  : (x : R) → add x zero ≡ x
    add-opp   : (x : R) → add x (opp x) ≡ zero
    opp-add   : (x y : R) → opp (add x y) ≡ add (opp x) (opp y)
    mul-comm  : (x y : R) → mul x y ≡ mul y x
    mul-assoc : (x y z : R) → mul (mul x y) z ≡ mul x (mul y z)
    mul-one   : (x : R) → mul x one ≡ x

    le-refl    : (x : R) → le x x
    le-trans   : (x y z : R) → le x y → le y z → le x z
    add-le-add : (a b c d : R) →
                 le a b → le c d → le (add a c) (add b d)

    abs-nonneg   : (x : R) → le zero (abs x)
    abs-triangle : (x y : R) →
                   le (abs (add x y)) (add (abs x) (abs y))
    abs-opp      : (x : R) → abs (opp x) ≡ abs x
    abs-sub-symm : (x y : R) →
                   abs (add x (opp y)) ≡ abs (add y (opp x))

    sub-decomp : (x y z : R) →
                 add x (opp z) ≡
                 add (add x (opp y)) (add y (opp z))
    sub-eq-zero : (x y : R) → add x (opp y) ≡ zero → x ≡ y

    eq-of-forall-eps2 : (x : R) →
      ((eps : R) → lt zero eps → le (abs x) (add eps eps)) →
      x ≡ zero

module Limits {R N : Set} (A : AbsField R N) where
  open AbsField A

  sub : R → R → R
  sub x y = add x (opp y)

  Limit : (N → R) → R → Set
  Limit u l =
    (eps : R) →
    lt zero eps →
    Σ N (λ cutoff →
      (n : N) →
      nat-le cutoff n →
      le (abs (sub (u n) l)) eps)

  sub-self-zero : Set
  sub-self-zero =
    (x : R) → sub x x ≡ zero

  sub-decomp-statement : Set
  sub-decomp-statement =
    (x y z : R) → sub x z ≡ add (sub x y) (sub y z)

  abs-sub-triangle : Set
  abs-sub-triangle =
    (x y z : R) →
    le (abs (sub x z)) (add (abs (sub x y)) (abs (sub y z)))

  abs-sub-nonneg : Set
  abs-sub-nonneg =
    (x y : R) → le zero (abs (sub x y))

  limit-unique : Set
  limit-unique =
    (u : N → R) (l m : R) →
    Limit u l →
    Limit u m →
    l ≡ m
