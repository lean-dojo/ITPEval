-- Statement-only formalization of Logipedia corpus artifact nat.lt_to_not_eq:
-- for all natural numbers n and m, n < m implies that n is not equal to m.
-- This file contains no proof.

module lt_to_not_eq where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤_ _<_

data ⊥ : Set where

Not : Set → Set
Not P = P → ⊥

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

lt-to-not-eq : Set
lt-to-not-eq =
  (n m : Nat) →
  n < m →
  Not (n ≡ m)
