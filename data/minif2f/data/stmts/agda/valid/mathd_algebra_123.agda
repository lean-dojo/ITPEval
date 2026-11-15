-- Statement-only formalization of miniF2F valid problem mathd_algebra_123. This file contains
-- no proof.

module mathd-algebra-123 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _+_; _-_; _*_; _<_)

NatLess : Nat → Nat → Set
NatLess m n = (m < n) ≡ true

mathd-algebra-123 : Set
mathd-algebra-123 =
  (a b : Nat) →
  NatLess zero a →
  NatLess zero b →
  a + b ≡ 20 →
  a ≡ 3 * b →
  a - b ≡ 10
