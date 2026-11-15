-- Statement-only formalization of miniF2F test problem imo_1974_p3. This file contains no
-- proof.

module imo-1974-p3 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _∣_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record _∣_ (d n : Nat) : Set where
  field
    quotient : Nat
    product  : d * quotient ≡ n

power : Nat → Nat → Nat
power base zero = 1
power base (suc exponent) = base * power base exponent

choose : Nat → Nat → Nat
choose zero zero = 1
choose zero (suc k) = 0
choose (suc n) zero = 1
choose (suc n) (suc k) = choose n k + choose n (suc k)

summand : Nat → Nat → Nat
summand n k =
  choose (2 * n + 1) (2 * k + 1) * power 2 (3 * k)

sumFromZeroInclusive : Nat → Nat → Nat
sumFromZeroInclusive n zero = summand n zero
sumFromZeroInclusive n (suc k) =
  sumFromZeroInclusive n k + summand n (suc k)

imo-1974-p3 : Set
imo-1974-p3 =
  (n : Nat) →
  Not (5 ∣ sumFromZeroInclusive n n)
