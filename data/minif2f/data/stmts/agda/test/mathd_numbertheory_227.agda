-- Statement-only formalization of miniF2F test problem mathd_numbertheory_227. This file
-- contains no proof.

module mathd-numbertheory-227 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _+_; _*_; _<_)

record Fraction : Set where
  constructor fraction
  field
    numerator   : Nat
    denominator : Nat

infixl 6 _+r_
infix 4 _≈r_

_+r_ : Fraction → Fraction → Fraction
fraction p d +r fraction q e =
  fraction (p * e + q * d) (d * e)

_≈r_ : Fraction → Fraction → Set
fraction p d ≈r fraction q e =
  p * e ≡ q * d

Positive : Nat → Set
Positive n = (zero < n) ≡ true

mathd-numbertheory-227 : Set
mathd-numbertheory-227 =
  (x y n : Nat) →
  Positive x →
  Positive y →
  Positive n →
  (fraction x 4 +r fraction y 6)
    ≈r fraction (x + y) n →
  n ≡ 5
