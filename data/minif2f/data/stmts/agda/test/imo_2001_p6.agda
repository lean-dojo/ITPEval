-- Statement-only formalization of miniF2F test problem imo_2001_p6. This file contains no
-- proof.

module imo-2001-p6 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _<_
infixr 3 _∨_

data ⊥ : Set where

data _<_ : Nat → Nat → Set where
  zero<succ : {n : Nat} → zero < suc n
  succ<succ : {m n : Nat} → m < n → suc m < suc n

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Divides (d n : Nat) : Set where
  field
    quotient : Nat
    product  : d * quotient ≡ n

record Prime (n : Nat) : Set where
  field
    at-least-two : 1 < n
    divisor-is-trivial :
      (d : Nat) →
      Divides d n →
      d ≡ 1 ∨ d ≡ n

imo-2001-p6 : Set
imo-2001-p6 =
  (a b c d : Nat) →
  zero < a →
  zero < b →
  zero < c →
  zero < d →
  d < c →
  c < b →
  b < a →
  a * c + b * d ≡
    (((b + d) + a) - c) * (((b + d) + c) - a) →
  Prime (a * b + c * d) →
  ⊥
