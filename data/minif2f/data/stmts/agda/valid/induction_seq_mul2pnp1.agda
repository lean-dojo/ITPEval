-- Statement-only formalization of miniF2F valid problem induction_seq_mul2pnp1. This file
-- contains no proof.

module induction_seq_mul2pnp1 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

induction_seq_mul2pnp1 : Set
induction_seq_mul2pnp1 =
  (n : Nat) →
  (u : Nat → Nat) →
  u 0 ≡ 0 →
  ((k : Nat) → u (k + 1) ≡ 2 * u k + (k + 1)) →
  u n ≡ 2 ^ (n + 1) - (n + 2)
