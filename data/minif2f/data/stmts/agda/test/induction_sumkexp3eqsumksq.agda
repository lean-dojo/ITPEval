-- Statement-only formalization of miniF2F test problem induction_sumkexp3eqsumksq. This file
-- contains no proof.

module induction_sumkexp3eqsumksq where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

sumTo : (Nat → Nat) → Nat → Nat
sumTo f zero = zero
sumTo f (suc n) = sumTo f n + f n

induction_sumkexp3eqsumksq : Set
induction_sumkexp3eqsumksq =
  (n : Nat) →
  sumTo (λ k → k ^ 3) n ≡ (sumTo (λ k → k) n) ^ 2
