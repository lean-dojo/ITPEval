-- Statement-only formalization of miniF2F valid problem mathd_algebra_15. This file contains no
-- proof.

module mathd-algebra-15 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _<_)

infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

Positive : Nat → Set
Positive n = (zero < n) ≡ true

mathd-algebra-15 : Set
mathd-algebra-15 =
  (s : Nat → Nat → Nat) →
  ((a b : Nat) →
    Positive a →
    Positive b →
    s a b ≡ a ^ b + b ^ a) →
  s 2 6 ≡ 100
