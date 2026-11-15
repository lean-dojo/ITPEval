-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_136. This file
-- contains no proof.

module mathd-numbertheory-136 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

mathd-numbertheory-136 : Set
mathd-numbertheory-136 =
  (n : Nat) →
  123 * n + 17 ≡ 39500 →
  n ≡ 321
