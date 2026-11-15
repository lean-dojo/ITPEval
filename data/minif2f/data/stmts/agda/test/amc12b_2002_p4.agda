-- Statement-only formalization of miniF2F test problem amc12b_2002_p4: a positive natural
-- denominator making 1/2 + 1/3 + 1/7 + 1/n an integer must equal 42. This file contains no proof.

module amc12b-2002-p4 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _+_; _*_; _<_)

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

Positive : Nat → Set
Positive n = (zero < n) ≡ true

IntegralReciprocalSum : Nat → Set
IntegralReciprocalSum n =
  Exists Nat λ k →
    21 * n + 14 * n + 6 * n + 42 ≡
    k * (42 * n)

amc12b-2002-p4 : Set
amc12b-2002-p4 =
  (n : Nat) →
  Positive n →
  IntegralReciprocalSum n →
  n ≡ 42
