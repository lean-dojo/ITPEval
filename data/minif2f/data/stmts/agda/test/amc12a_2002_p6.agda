-- Statement-only formalization of miniF2F test problem amc12a_2002_p6. This file contains no
-- proof.

module amc12a-2002-p6 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _<_)

infix 4 _≤_
infixr 4 _∧_

_≤_ : Nat → Nat → Set
m ≤ n = (m < suc n) ≡ true

record _∧_ (A B : Set) : Set where
  constructor conjunction
  field
    left  : A
    right : B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

amc12a-2002-p6 : Set
amc12a-2002-p6 =
  (n : Nat) →
  (zero < n) ≡ true →
  Exists Nat λ m →
    ((n < m) ≡ true) ∧
    Exists Nat λ p →
      m * p ≤ m + p
