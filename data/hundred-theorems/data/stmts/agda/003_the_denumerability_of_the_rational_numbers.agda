-- Statement-only formalization of "The Denumerability of the Rational Numbers" from Hundred
-- Theorems item 003. This file contains no proof.

module DenumerabilityRationals where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _≈_

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

scale : Int → Nat → Int
scale (pos m) n = pos (m * n)
scale (negsuc m) n = negative (suc m * n)

record Fraction : Set where
  constructor fraction
  field
    numerator : Int
    denominator-minus-one : Nat

denominator : Fraction → Nat
denominator q = suc (Fraction.denominator-minus-one q)

_≈_ : Fraction → Fraction → Set
x ≈ y =
  scale (Fraction.numerator x) (denominator y) ≡
  scale (Fraction.numerator y) (denominator x)

record Exists (A : Set) (P : A → Set) : Set where
  constructor exists
  field
    exists-value : A
    exists-property : P exists-value

record ExistsUnique (A : Set) (P : A → Set) : Set where
  constructor exists-unique
  field
    unique-value : A
    unique-property : P unique-value
    uniqueness : (x : A) → P x → x ≡ unique-value

denumerability-of-rational-numbers : Set
denumerability-of-rational-numbers =
  Exists (Nat → Fraction) (λ enumerate →
    (q : Fraction) →
    ExistsUnique Nat (λ n → enumerate n ≈ q))
