-- Statement-only formalization of miniF2F test problem induction_nfactltnexpnm1ngt3. This file
-- contains no proof.

module induction_nfactltnexpnm1ngt3 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _-_)

infix 4 _≤_ _<_
infixr 8 _^_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

factorial : Nat → Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

induction_nfactltnexpnm1ngt3 : Set
induction_nfactltnexpnm1ngt3 =
  (n : Nat) →
  3 ≤ n →
  factorial n < n ^ (n - 1)
