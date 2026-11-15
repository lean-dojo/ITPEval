-- Statement-only formalization of miniF2F test problem mathd_algebra_158. This file contains no
-- proof.

module mathd-algebra-158 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value : A
    property : P value

Even : Nat → Set
Even n = Exists Nat (λ k → 2 * k ≡ n)

sumFirst : Nat → (Nat → Nat) → Nat
sumFirst zero f = zero
sumFirst (suc n) f = sumFirst n f + f n

mathd-algebra-158 : Set
mathd-algebra-158 =
  (a : Nat) →
  Even a →
  sumFirst 8 (λ k → 2 * k + 1) ≡
    sumFirst 5 (λ k → a + 2 * k) + 4 →
  a ≡ 8
