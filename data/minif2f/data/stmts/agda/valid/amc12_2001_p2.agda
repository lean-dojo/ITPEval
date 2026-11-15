-- Statement-only formalization of miniF2F valid problem amc12_2001_p2. This file contains no
-- proof.

module amc12-2001-p2 where

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

amc12-2001-p2 : Set
amc12-2001-p2 =
  (a b n : Nat) →
  (1 ≤ a ∧ a ≤ 9) →
  (0 ≤ b ∧ b ≤ 9) →
  n ≡ 10 * a + b →
  n ≡ a * b + a + b →
  b ≡ 9
