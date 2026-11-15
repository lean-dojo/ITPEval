-- Statement-only formalization of miniF2F valid problem amc12a_2003_p1. This file contains no
-- proof.

module amc12a-2003-p1 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

sumFirst : Nat → (Nat → Nat) → Nat
sumFirst zero term = zero
sumFirst (suc n) term = sumFirst n term + term n

amc12a-2003-p1 : Set
amc12a-2003-p1 =
  (u v : Nat → Nat) →
  ((n : Nat) → u n ≡ 2 * n + 2) →
  ((n : Nat) → v n ≡ 2 * n + 1) →
  sumFirst 2003 u - sumFirst 2003 v ≡ 2003
