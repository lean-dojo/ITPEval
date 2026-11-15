-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_22. This file
-- contains no proof.

module mathd-numbertheory-22 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤_ _<_
infixr 2 _∨_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

record IsSquare (n : Nat) : Set where
  field
    root : Nat
    root-squared : root * root ≡ n

mathd-numbertheory-22 : Set
mathd-numbertheory-22 =
  (b : Nat) →
  b < 10 →
  IsSquare (10 * b + 6) →
  (b ≡ 3) ∨ (b ≡ 1)
