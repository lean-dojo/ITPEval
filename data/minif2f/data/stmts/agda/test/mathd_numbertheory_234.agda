-- Statement-only formalization of miniF2F test problem mathd_numbertheory_234. This file
-- contains no proof.

module mathd-numbertheory-234 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤_
infixr 3 _∧_
infixr 8 _^_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    left : A
    right : B

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

mathd-numbertheory-234 : Set
mathd-numbertheory-234 =
  (a b : Nat) →
  (1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9) →
  (10 * a + b) ^ 3 ≡ 912673 →
  a + b ≡ 16
