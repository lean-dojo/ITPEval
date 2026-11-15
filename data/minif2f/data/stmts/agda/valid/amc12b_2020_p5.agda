-- Statement-only formalization of miniF2F valid problem amc12b_2020_p5:
-- two exact fractional relations between natural numbers determine the first
-- number as 42. This file contains no proof.

module amc12b-2020-p5 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

-- Clearing the positive denominator 24 in the source rational equations gives
-- the following equivalent natural-number equalities.
amc12b-2020-p5 : Set
amc12b-2020-p5 =
  (a b : Nat) →
  15 * b ≡ 16 * a + 168 →
  9 * b ≡ 8 * a + 168 →
  a ≡ 42
