-- Statement-only formalization of miniF2F test problem mathd_numbertheory_314. This file
-- contains no proof.

module mathd-numbertheory-314 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; mod-helper)

infix 4 _≤_ _<_ _∣_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-314 : Set
mathd-numbertheory-314 =
  (r n : Nat) →
  r ≡ naturalMod 1342 13 →
  zero < n →
  1342 ∣ n →
  naturalMod n 13 < r →
  6710 ≤ n
