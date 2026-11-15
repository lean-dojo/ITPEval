-- Statement-only formalization of PutnamBench corpus artifact putnam_1969_b1:
-- if n is positive and 24 divides n + 1, then 24 divides the sum of all
-- positive divisors of n. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infix 4 _∣_

data Positive : Nat → Set where
  positive : {n : Nat} → Positive (suc n)

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    division-equation : divisor * quotient ≡ dividend

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

putnam-1969-b1 : Set
putnam-1969-b1 =
  (n : Nat) →
  Positive n →
  24 ∣ (n + 1) →
  24 ∣ sumDivisors n
