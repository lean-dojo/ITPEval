-- Statement-only formalization of PutnamBench corpus artifact putnam_1976_b6:
-- every quasiperfect natural number, whose positive divisors sum to one more
-- than twice the number, is the square of an odd integer. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc n) = false
natEqual (suc m) zero = false
natEqual (suc m) (suc n) = natEqual m n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

sumDivisorsUpTo : Nat → Nat → Nat
sumDivisorsUpTo number zero = zero
sumDivisorsUpTo number (suc bound)
  with natEqual (naturalMod number (suc bound)) zero
... | true = suc bound + sumDivisorsUpTo number bound
... | false = sumDivisorsUpTo number bound

sumDivisors : Nat → Nat
sumDivisors number = sumDivisorsUpTo number number

Odd : Nat → Set
Odd m =
  Exists Nat (λ k → m ≡ suc (2 * k))

putnam-1976-b6 : Set
putnam-1976-b6 =
  (N : Nat) →
  sumDivisors N ≡ 2 * N + 1 →
  Exists Nat (λ m → Odd m and (m * m ≡ N))
