-- Statement-only formalization of miniF2F test problem mathd_numbertheory_521. This file
-- contains no proof.

module mathd-numbertheory-521 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _-_; _*_)

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value : A
    property : P value

Even : Nat → Set
Even n = Exists Nat (λ k → 2 * k ≡ n)

mathd-numbertheory-521 : Set
mathd-numbertheory-521 =
  (m n : Nat) →
  Even m →
  Even n →
  m - n ≡ 2 →
  m * n ≡ 288 →
  m ≡ 18
