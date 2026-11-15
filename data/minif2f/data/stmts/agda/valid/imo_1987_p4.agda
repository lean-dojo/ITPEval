-- Statement-only formalization of miniF2F valid problem imo_1987_p4. This file contains no
-- proof.

module imo-1987-p4 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)

infix 4 _≠_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    evidence : P value

imo-1987-p4 : Set
imo-1987-p4 =
  (f : Nat → Nat) →
  Exists Nat (λ n → f (f n) ≠ n + 1987)
