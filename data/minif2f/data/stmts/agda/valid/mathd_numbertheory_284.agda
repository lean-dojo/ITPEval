-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_284. This file
-- contains no proof.

module mathd-numbertheory-284 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤_
infixr 3 _∧_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

record _∧_ (A B : Set) : Set where
  constructor conjunction
  field
    left  : A
    right : B

mathd-numbertheory-284 : Set
mathd-numbertheory-284 =
  (a b : Nat) →
  (1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9) →
  10 * a + b ≡ 2 * (a + b) →
  10 * a + b ≡ 18
