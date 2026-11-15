-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_405:
-- for a natural-valued Fibonacci recurrence, indices congruent to 5, 10, and 15
-- modulo 16 yield a three-term value sum congruent to 5 modulo 7. This file contains
-- no proof.

module mathd-numbertheory-405 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; mod-helper)

infix 4 _≤_ _<_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-405 : Set
mathd-numbertheory-405 =
  (a b c : Nat) →
  (t : Nat → Nat) →
  t 0 ≡ 0 →
  t 1 ≡ 1 →
  ((n : Nat) →
    1 < n →
    t n ≡ t (n - 2) + t (n - 1)) →
  naturalMod a 16 ≡ 5 →
  naturalMod b 16 ≡ 10 →
  naturalMod c 16 ≡ 15 →
  naturalMod (t a + t b + t c) 7 ≡ 5
