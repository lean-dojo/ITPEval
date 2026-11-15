-- Statement-only formalization of miniF2F test problem aime_1984_p1. This file contains no
-- proof.

module aime-1984-p1 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

record Rat : Set where
  constructor fraction
  field
    positive-part : Nat
    negative-part : Nat
    denominator-minus-one : Nat

predecessor : Nat → Nat
predecessor zero = zero
predecessor (suc n) = n

infixl 6 _+r_

_+r_ : Rat → Rat → Rat
fraction p n d +r fraction q m e =
  fraction
    (p * suc e + q * suc d)
    (n * suc e + m * suc d)
    (predecessor (suc d * suc e))

fromNat : Nat → Rat
fromNat n = fraction n zero zero

infix 4 _≈_

_≈_ : Rat → Rat → Set
fraction p n d ≈ fraction q m e =
  (p * suc e + m * suc d) ≡ (q * suc d + n * suc e)

sumFromOne : Nat → (Nat → Rat) → Rat
sumFromOne zero u = fromNat zero
sumFromOne (suc n) u = sumFromOne n u +r u (suc n)

sumEvenFromTwo : Nat → (Nat → Rat) → Rat
sumEvenFromTwo zero u = fromNat zero
sumEvenFromTwo (suc n) u =
  sumEvenFromTwo n u +r u (2 * suc n)

aime-1984-p1 : Set
aime-1984-p1 =
  (u : Nat → Rat) →
  ((n : Nat) → u (suc n) ≈ (u n +r fromNat 1)) →
  sumFromOne 98 u ≈ fromNat 137 →
  sumEvenFromTwo 49 u ≈ fromNat 93
