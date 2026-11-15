-- Statement-only formalization of Hundred Theorems artifact hundred-theorems__agda__033,
-- "Fermat's Last Theorem": no positive natural bases satisfy a^n + b^n = c^n for a
-- natural exponent n > 2. This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤_ _<_
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
base ^ suc exponent = base * (base ^ exponent)

fermat-s-last-theorem : Set
fermat-s-last-theorem =
  (n a b c : Nat) →
  2 < n →
  zero < a →
  zero < b →
  zero < c →
  Not (a ^ n + b ^ n ≡ c ^ n)
