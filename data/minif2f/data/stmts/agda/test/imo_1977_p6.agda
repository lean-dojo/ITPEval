-- Statement-only formalization of miniF2F test problem imo_1977_p6. This file contains no
-- proof.

module imo-1977-p6 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _<_)

imo-1977-p6 : Set
imo-1977-p6 =
  (f : Nat → Nat) →
  ((n : Nat) → (zero < f n) ≡ true) →
  ((n : Nat) →
    (zero < n) ≡ true →
    (f (f n) < f (suc n)) ≡ true) →
  (n : Nat) →
  (zero < n) ≡ true →
  f n ≡ n
