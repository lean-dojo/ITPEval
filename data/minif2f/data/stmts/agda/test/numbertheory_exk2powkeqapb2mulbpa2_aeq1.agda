-- Statement-only formalization of miniF2F test problem numbertheory_exk2powkeqapb2mulbpa2_aeq1.
-- This file contains no proof.

module numbertheory_exk2powkeqapb2mulbpa2_aeq1 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 4 _∧_
infixr 8 _^_

data Positive : Nat → Set where
  positive : {n : Nat} → Positive (suc n)

record _∧_ (A B : Set) : Set where
  constructor conjunction
  field
    left  : A
    right : B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

numbertheory_exk2powkeqapb2mulbpa2_aeq1 : Set
numbertheory_exk2powkeqapb2mulbpa2_aeq1 =
  (a b : Nat) →
  (Positive a ∧ Positive b) →
  Exists Nat
    (λ k →
      Positive k ∧
      (2 ^ k ≡ (a + b ^ 2) * (b + a ^ 2))) →
  a ≡ 1
