-- Statement-only formalization of miniF2F valid problem induction_ineq_nsqlefactn. This file
-- contains no proof.

module induction_ineq_nsqlefactn where

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _≤_
infixr 8 _^_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

factorial : Nat → Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

induction_ineq_nsqlefactn : Set
induction_ineq_nsqlefactn =
  (n : Nat) →
  4 ≤ n →
  n ^ 2 ≤ factorial n
