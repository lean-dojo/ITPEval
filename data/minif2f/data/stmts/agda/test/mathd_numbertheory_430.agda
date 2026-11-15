-- Statement-only formalization of miniF2F test problem mathd_numbertheory_430. This file
-- contains no proof.

module mathd-numbertheory-430 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _≤_ _≠_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

mathd-numbertheory-430 : Set
mathd-numbertheory-430 =
  (a b c : Nat) →
  1 ≤ a →
  a ≤ 9 →
  1 ≤ b →
  b ≤ 9 →
  1 ≤ c →
  c ≤ 9 →
  a ≠ b →
  a ≠ c →
  b ≠ c →
  a + b ≡ c →
  10 * a + a - b ≡ 2 * c →
  c * b ≡ 10 * a + a + a →
  a + b + c ≡ 8
