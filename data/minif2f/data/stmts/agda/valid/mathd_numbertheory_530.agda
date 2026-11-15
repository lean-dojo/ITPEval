-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_530. This file
-- contains no proof.

module mathd-numbertheory-530 where

open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper; mod-helper)

infix 4 _≤_ _<_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

naturalDiv : Nat → Nat → Nat
naturalDiv numerator zero = zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

gcdWithFuel : Nat → Nat → Nat → Nat
gcdWithFuel zero a b = a
gcdWithFuel (suc fuel) a zero = a
gcdWithFuel (suc fuel) a (suc b) =
  gcdWithFuel fuel (suc b) (naturalMod a (suc b))

naturalGCD : Nat → Nat → Nat
naturalGCD a b =
  gcdWithFuel (suc (a + b)) a b

naturalLCM : Nat → Nat → Nat
naturalLCM a b =
  naturalDiv (a * b) (naturalGCD a b)

mathd-numbertheory-530 : Set
mathd-numbertheory-530 =
  (n k : Nat) →
  zero < n →
  zero < k →
  5 * k < n →
  n < 6 * k →
  22 ≤ naturalDiv (naturalLCM n k) (naturalGCD n k)
