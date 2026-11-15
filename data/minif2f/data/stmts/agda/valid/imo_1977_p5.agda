-- Statement-only formalization of miniF2F valid problem imo_1977_p5. This file contains no
-- proof.

module imo-1977-p5 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _≤_ _<_
infixr 3 _∧_
infixr 2 _∨_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

record _∧_ (A B : Set) : Set where
  constructor conjunction
  field
    left  : A
    right : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

square : Nat → Nat
square n = n * n

absoluteDifference : Nat → Nat → Nat
absoluteDifference m n = (m - n) + (n - m)

imo-1977-p5 : Set
imo-1977-p5 =
  (a b q r : Nat) →
  r < a + b →
  square a + square b ≡ (a + b) * q + r →
  square q + r ≡ 1977 →
  (absoluteDifference a 22 ≡ 15 ∧
   absoluteDifference b 22 ≡ 28) ∨
  (absoluteDifference a 22 ≡ 28 ∧
   absoluteDifference b 22 ≡ 15)
