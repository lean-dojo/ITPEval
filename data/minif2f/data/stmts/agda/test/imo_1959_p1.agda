-- Statement-only formalization of miniF2F test problem imo_1959_p1. This file contains no
-- proof.

module imo-1959-p1 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

record Divides (d n : Nat) : Set where
  field
    quotient : Nat
    product  : d * quotient ≡ n

Coprime : Nat → Nat → Set
Coprime m n =
  (d : Nat) →
  Divides d m →
  Divides d n →
  d ≡ 1

imo-1959-p1 : Set
imo-1959-p1 =
  (n : Nat) →
  Coprime (21 * n + 4) (14 * n + 3)
