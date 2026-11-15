-- Statement-only formalization of miniF2F valid problem numbertheory_sumkmulnckeqnmul2pownm1.
-- This file contains no proof.

module numbertheory_sumkmulnckeqnmul2pownm1 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _≤_ _<_
infixr 8 _^_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

choose : Nat → Nat → Nat
choose zero zero = 1
choose zero (suc k) = 0
choose (suc n) zero = 1
choose (suc n) (suc k) = choose n k + choose n (suc k)

sumFromOne : Nat → (Nat → Nat) → Nat
sumFromOne zero term = zero
sumFromOne (suc n) term = sumFromOne n term + term (suc n)

numbertheory_sumkmulnckeqnmul2pownm1 : Set
numbertheory_sumkmulnckeqnmul2pownm1 =
  (n : Nat) →
  zero < n →
  sumFromOne n (λ k → k * choose n k) ≡ n * (2 ^ (n - 1))
