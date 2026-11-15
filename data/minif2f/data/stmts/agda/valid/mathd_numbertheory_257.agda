-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_257. This file
-- contains no proof.

module mathd-numbertheory-257 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _≤_ _∣_
infixr 3 _∧_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    left  : A
    right : B

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

sumFirst : Nat → (Nat → Nat) → Nat
sumFirst zero term = zero
sumFirst (suc n) term = sumFirst n term + term n

mathd-numbertheory-257 : Set
mathd-numbertheory-257 =
  (x : Nat) →
  ((1 ≤ x) ∧ (x ≤ 100)) →
  77 ∣ (sumFirst 101 (λ k → k) - x) →
  x ≡ 45
