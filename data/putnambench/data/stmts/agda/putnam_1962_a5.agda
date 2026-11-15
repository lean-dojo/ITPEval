-- Statement-only formalization of PutnamBench corpus artifact putnam_1962_a5:
-- for every natural n at least two, the binomial sum from k = 1 through n of
-- (n choose k) k squared has the stated closed form. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _≤_

data _≤_ : Nat → Nat → Set where
  zero≤   : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

one : Nat
one = suc zero

two : Nat
two = suc one

power : Nat → Nat → Nat
power base zero = one
power base (suc exponent) = power base exponent * base

choose : Nat → Nat → Nat
choose n zero = one
choose zero (suc k) = zero
choose (suc n) (suc k) = choose n (suc k) + choose n k

sum-from-one-through : Nat → (Nat → Nat) → Nat
sum-from-one-through zero term = zero
sum-from-one-through (suc n) term =
  sum-from-one-through n term + term (suc n)

putnam-1962-a5-solution : Nat → Nat
putnam-1962-a5-solution n =
  (n * (n + one)) * power two (n - two)

putnam-1962-a5 : Set
putnam-1962-a5 =
  (n : Nat) →
  two ≤ n →
  putnam-1962-a5-solution n
    ≡
  sum-from-one-through n
    (λ k → choose n k * power k two)
