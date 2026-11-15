-- Statement-only formalization of miniF2F valid problem imo_1987_p6. This file contains no
-- proof.

module imo-1987-p6 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _≤_ _∣_
infixr 3 _∨_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

record Prime (n : Nat) : Set where
  field
    at-least-two : 2 ≤ n
    divisor-is-trivial :
      (d : Nat) →
      d ∣ n →
      d ≡ 1 ∨ d ≡ n

quadratic : Nat → Nat → Nat
quadratic p k = k * k + k + p

BelowSqrtThird : Nat → Nat → Set
BelowSqrtThird k p = 3 * (k * k) ≤ p

imo-1987-p6 : Set
imo-1987-p6 =
  (p : Nat) →
  (f : Nat → Nat) →
  2 ≤ p →
  ((x : Nat) → f x ≡ quadratic p x) →
  ((k : Nat) → BelowSqrtThird k p → Prime (f k)) →
  (i : Nat) →
  i ≤ p - 2 →
  Prime (f i)
