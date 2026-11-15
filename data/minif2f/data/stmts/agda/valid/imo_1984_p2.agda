-- Statement-only formalization of miniF2F valid problem imo_1984_p2. This file contains no
-- proof.

module imo-1984-p2 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _≤_ _<_ _∣_
infixr 8 _^_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

imo-1984-p2 : Set
imo-1984-p2 =
  (a b : Nat) →
  zero < a →
  zero < b →
  Not (7 ∣ a) →
  Not (7 ∣ b) →
  Not (7 ∣ (a + b)) →
  (7 ^ 7) ∣ (((a + b) ^ 7 - a ^ 7) - b ^ 7) →
  19 ≤ a + b
