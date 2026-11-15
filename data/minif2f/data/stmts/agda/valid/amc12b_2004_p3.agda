-- Statement-only formalization of miniF2F valid problem amc12b_2004_p3. This file contains no
-- proof.

module amc12b-2004-p3 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

amc12b-2004-p3 : Set
amc12b-2004-p3 =
  (x y : Nat) →
  2 ^ x * 3 ^ y ≡ 1296 →
  x + y ≡ 8
