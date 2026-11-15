-- Statement-only formalization of miniF2F test problem amc12_2000_p6. This file contains no
-- proof.

module amc12-2000-p6 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _-_; _*_; _<_)

infix 4 _≤_ _≠_
infixr 3 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

_≤_ : Nat → Nat → Set
m ≤ n = (m < suc n) ≡ true

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Divides (d n : Nat) : Set where
  field
    quotient : Nat
    product  : d * quotient ≡ n

record Prime (n : Nat) : Set where
  field
    at-least-two : 2 ≤ n
    divisor-is-trivial :
      (d : Nat) →
      Divides d n →
      d ≡ 1 ∨ d ≡ n

amc12-2000-p6 : Set
amc12-2000-p6 =
  (p q : Nat) →
  Prime p →
  Prime q →
  4 ≤ p →
  p ≤ 18 →
  4 ≤ q →
  q ≤ 18 →
  p * q - (p + q) ≠ 194
