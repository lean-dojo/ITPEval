-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_629. This file
-- contains no proof.

module mathd-numbertheory-629 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _≤_ _<_ _∣_
infixr 8 _^_

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

record IsLCM (a b l : Nat) : Set where
  field
    lcm-left-divides : a ∣ l
    lcm-right-divides : b ∣ l
    least-common-multiple :
      (m : Nat) →
      a ∣ m →
      b ∣ m →
      l ∣ m

record Satisfies (t : Nat) : Set where
  field
    positive : zero < t
    lcm-value : Nat
    lcm-specification : IsLCM 12 t lcm-value
    power-equation : lcm-value ^ 3 ≡ (12 * t) ^ 2

record IsLeast (P : Nat → Set) (n : Nat) : Set where
  field
    member : P n
    lower-bound : (m : Nat) → P m → n ≤ m

mathd-numbertheory-629 : Set
mathd-numbertheory-629 = IsLeast Satisfies 18
