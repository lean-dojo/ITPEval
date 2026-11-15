-- Statement-only formalization of miniF2F artifact amc12a_2008_p15: for
-- k = 2008 ^ 2 + 2 ^ 2008, the natural number k ^ 2 + 2 ^ k has remainder
-- 6 modulo 10. This file contains no proof.

module amc12a-2008-p15 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

amc12a-2008-p15 : Set
amc12a-2008-p15 =
  (k : Nat) →
  k ≡ 2008 ^ 2 + 2 ^ 2008 →
  naturalMod (k ^ 2 + 2 ^ k) 10 ≡ 6
