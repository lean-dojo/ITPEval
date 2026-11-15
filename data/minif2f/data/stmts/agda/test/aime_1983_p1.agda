-- Statement-only formalization of miniF2F test problem aime_1983_p1. This file contains no
-- proof.

module aime-1983-p1 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _<_)

infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

aime-1983-p1 : Set
aime-1983-p1 =
  (x y z w : Nat) →
  (1 < x) ≡ true →
  (1 < y) ≡ true →
  (1 < z) ≡ true →
  (0 < suc w) ≡ true →
  x ^ 24 ≡ w →
  y ^ 40 ≡ w →
  (x * y * z) ^ 12 ≡ w →
  z ^ 60 ≡ w
