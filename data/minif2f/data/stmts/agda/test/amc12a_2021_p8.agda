-- Statement-only formalization of miniF2F test problem amc12a_2021_p8. This file contains no
-- proof.

module amc12a-2021-p8 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _≤_
infixr 3 _∧_

data _≤_ : Nat → Nat → Set where
  zero≤    : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

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

Even : Nat → Set
Even n = Exists Nat (λ k → 2 * k ≡ n)

Odd : Nat → Set
Odd n = Exists Nat (λ k → 2 * k + 1 ≡ n)

amc12a-2021-p8 : Set
amc12a-2021-p8 =
  (d : Nat → Nat) →
  d 0 ≡ 0 →
  d 1 ≡ 0 →
  d 2 ≡ 1 →
  ((n : Nat) →
    3 ≤ n →
    d n ≡ d (n - 1) + d (n - 3)) →
  Even (d 2021) ∧
  Odd (d 2022) ∧
  Even (d 2023)
