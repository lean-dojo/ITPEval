-- Statement-only formalization of miniF2F valid artifact induction_sum2kp1npqsqm1:
-- the finite sum of 2 * k + 3 for k below n equals (n + 1) squared minus 1.
-- This file contains no proof.

module induction_sum2kp1npqsqm1 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

sumFirst : Nat → (Nat → Nat) → Nat
sumFirst zero term = zero
sumFirst (suc n) term = sumFirst n term + term n

induction_sum2kp1npqsqm1 : Set
induction_sum2kp1npqsqm1 =
  (n : Nat) →
  sumFirst n (λ k → 2 * k + 3) ≡ (n + 1) ^ 2 - 1
