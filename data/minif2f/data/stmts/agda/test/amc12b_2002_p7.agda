-- Statement-only formalization of miniF2F test problem amc12b_2002_p7. This file contains no
-- proof.

module amc12b-2002-p7 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _+_; _*_; _<_)

Positive : Nat → Set
Positive n = (zero < n) ≡ true

amc12b-2002-p7 : Set
amc12b-2002-p7 =
  (a b c : Nat) →
  Positive a →
  Positive b →
  Positive c →
  b ≡ a + 1 →
  c ≡ b + 1 →
  (a * b) * c ≡ 8 * ((a + b) + c) →
  (a * a) + ((b * b) + (c * c)) ≡ 77
