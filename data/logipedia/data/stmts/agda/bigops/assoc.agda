-- Statement-only formalization of Logipedia corpus artifact bigops.assoc
-- (catalog title "bigops.assoc"): associativity of multiplication on natural
-- numbers. This file contains no proof.

module assoc where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _*_)

bigops-assoc : Set
bigops-assoc =
  (a b c : Nat) →
  a * (b * c) ≡ (a * b) * c
