-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_326. This file
-- contains no proof.

module mathd-numbertheory-326 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_; _-_; _*_)

mathd-numbertheory-326 : Set
mathd-numbertheory-326 =
  (n : Nat) →
  (n - 1) * n * (n + 1) ≡ 720 →
  n + 1 ≡ 10
