-- Statement-only formalization of miniF2F test problem mathd_numbertheory_150. This file
-- contains no proof.

module mathd-numbertheory-150 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤_ _∣_
infixr 3 _∨_

data ⊥ : Set where

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Prime (n : Nat) : Set where
  field
    at-least-two : 2 ≤ n
    divisor-is-trivial :
      (d : Nat) →
      d ∣ n →
      d ≡ 1 ∨ d ≡ n

mathd-numbertheory-150 : Set
mathd-numbertheory-150 =
  (n : Nat) →
  (Prime (7 + 30 * n) → ⊥) →
  6 ≤ n
