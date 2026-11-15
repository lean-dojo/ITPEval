-- Statement-only formalization of miniF2F test problem amc12a_2003_p5. This file contains no
-- proof.

module amc12a-2003-p5 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_; _<_)

infix 4 _≤_

_≤_ : Nat → Nat → Set
m ≤ n = (m < suc n) ≡ true

Digit : Nat → Set
Digit digit = digit ≤ 9

fiveDigit : Nat → Nat → Nat → Nat → Nat → Nat
fiveDigit tenThousands thousands hundreds tens units =
  10000 * tenThousands +
  1000 * thousands +
  100 * hundreds +
  10 * tens +
  units

amc12a-2003-p5 : Set
amc12a-2003-p5 =
  (A M C : Nat) →
  Digit A →
  Digit M →
  Digit C →
  fiveDigit A M C 1 0 + fiveDigit A M C 1 2 ≡ 123422 →
  A + M + C ≡ 14
