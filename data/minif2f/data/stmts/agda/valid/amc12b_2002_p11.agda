-- Statement-only formalization of miniF2F valid artifact amc12b_2002_p11: a primality
-- implication for natural-number sums and truncated subtraction. This file contains no proof.

module amc12b-2002-p11 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _≤_ _∣_
infixr 3 _∨_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

record Prime (n : Nat) : Set where
  field
    at-least-two : 2 ≤ n
    divisor-is-trivial :
      (d : Nat) →
      d ∣ n →
      d ≡ 1 ∨ d ≡ n

amc12b-2002-p11 : Set
amc12b-2002-p11 =
  (a b : Nat) →
  Prime a →
  Prime b →
  Prime (a + b) →
  Prime (a - b) →
  Prime (a + b + (a - b + (a + b)))
