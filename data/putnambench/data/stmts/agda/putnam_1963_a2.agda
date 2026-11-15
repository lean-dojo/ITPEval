-- Statement-only formalization of PutnamBench corpus artifact putnam_1963_a2:
-- a positive, strictly increasing natural-number function that fixes 2 and is
-- multiplicative on coprime positive inputs is the identity on positive
-- naturals. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _≤_ _<_ _∣_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

record IsGCD (a b g : Nat) : Set where
  field
    gcd-divides-left : g ∣ a
    gcd-divides-right : g ∣ b
    greatest-common-divisor :
      (d : Nat) →
      d ∣ a →
      d ∣ b →
      d ∣ g

Coprime : Nat → Nat → Set
Coprime m n = IsGCD m n 1

putnam-1963-a2 : Set
putnam-1963-a2 =
  (f : Nat → Nat) →
  ((n : Nat) → zero < f n) →
  ((i j : Nat) → zero < i → i < j → f i < f j) →
  f 2 ≡ 2 →
  ((m n : Nat) →
    zero < m →
    zero < n →
    Coprime m n →
    f (m * n) ≡ f m * f n) →
  (n : Nat) →
  zero < n →
  f n ≡ n
