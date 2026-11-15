-- Statement-only formalization of miniF2F valid problem induction_sum_odd. This file contains
-- no proof.

module induction_sum_odd where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

sumFirst : Nat → (Nat → Nat) → Nat
sumFirst zero term = zero
sumFirst (suc n) term = sumFirst n term + term n

induction_sum_odd : Set
induction_sum_odd =
  (n : Nat) →
  sumFirst n (λ k → 2 * k + 1) ≡ n ^ 2
