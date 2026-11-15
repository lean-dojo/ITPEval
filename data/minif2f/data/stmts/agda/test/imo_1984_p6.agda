-- Statement-only formalization of miniF2F test problem imo_1984_p6. This file contains no
-- proof.

module imo-1984-p6 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _<_)

infixr 3 _∧_
infixr 8 _^_

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

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

Odd : Nat → Set
Odd n = Exists Nat (λ t → 2 * t + 1 ≡ n)

imo-1984-p6 : Set
imo-1984-p6 =
  (a b c d k m : Nat) →
  (((zero < a) ≡ true) ∧
   ((zero < b) ≡ true) ∧
   ((zero < c) ≡ true) ∧
   ((zero < d) ≡ true)) →
  (Odd a ∧ Odd b ∧ Odd c ∧ Odd d) →
  (((a < b) ≡ true) ∧
   ((b < c) ≡ true) ∧
   ((c < d) ≡ true)) →
  a * d ≡ b * c →
  a + d ≡ 2 ^ k →
  b + c ≡ 2 ^ m →
  a ≡ 1
