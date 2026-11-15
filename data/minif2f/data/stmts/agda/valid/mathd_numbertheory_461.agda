-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_461. This file
-- contains no proof.

module mathd-numbertheory-461 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc n) = false
natEqual (suc m) zero = false
natEqual (suc m) (suc n) = natEqual m n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

gcdWithFuel : Nat → Nat → Nat → Nat
gcdWithFuel zero a b = a
gcdWithFuel (suc fuel) a zero = a
gcdWithFuel (suc fuel) a (suc b) =
  gcdWithFuel fuel (suc b) (naturalMod a (suc b))

naturalGCD : Nat → Nat → Nat
naturalGCD a b =
  gcdWithFuel (suc (a + b)) a b

power : Nat → Nat → Nat
power base zero = 1
power base (suc exponent) = base * power base exponent

filterList : {A : Set} → (A → Bool) → List A → List A
filterList predicate [] = []
filterList predicate (x ∷ xs) with predicate x
... | true = x ∷ filterList predicate xs
... | false = filterList predicate xs

length : {A : Set} → List A → Nat
length [] = zero
length (x ∷ xs) = suc (length xs)

coprimeToEight : Nat → Bool
coprimeToEight x = natEqual (naturalGCD x 8) 1

oneThroughSeven : List Nat
oneThroughSeven = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ []

mathd-numbertheory-461 : Set
mathd-numbertheory-461 =
  (n : Nat) →
  n ≡ length (filterList coprimeToEight oneThroughSeven) →
  naturalMod (power 3 n) 8 ≡ 1
