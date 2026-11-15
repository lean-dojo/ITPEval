-- Statement-only formalization of PutnamBench corpus artifact putnam_2021_a5:
-- the power sum over the positive integers at most 2021 that are coprime to
-- 2021 is divisible by 2021 exactly for exponents divisible by neither 42 nor
-- 46. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infix 4 _∣_ _↔_
infixr 5 _×_
infixr 8 _^_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

record _×_ (A B : Set) : Set where
  field
    first : A
    second : B

record _↔_ (A B : Set) : Set where
  field
    forward : A -> B
    backward : B -> A

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

natEqual : Nat -> Nat -> Bool
natEqual zero zero = true
natEqual zero (suc n) = false
natEqual (suc m) zero = false
natEqual (suc m) (suc n) = natEqual m n

ifNat : Bool -> Nat -> Nat -> Nat
ifNat true when-true when-false = when-true
ifNat false when-true when-false = when-false

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

gcdWithFuel : Nat -> Nat -> Nat -> Nat
gcdWithFuel zero a b = a
gcdWithFuel (suc fuel) a zero = a
gcdWithFuel (suc fuel) a (suc b) =
  gcdWithFuel fuel (suc b) (naturalMod a (suc b))

euclideanGCD : Nat -> Nat -> Nat
euclideanGCD a b =
  gcdWithFuel (suc (a + b)) a b

_^_ : Nat -> Nat -> Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

sumCoprimePowersUpTo : Nat -> Nat -> Nat
sumCoprimePowersUpTo zero exponent = zero
sumCoprimePowersUpTo (suc n) exponent =
  sumCoprimePowersUpTo n exponent
  + ifNat
      (natEqual (euclideanGCD (suc n) 2021) 1)
      ((suc n) ^ exponent)
      zero

putnam-2021-a5 : Set
putnam-2021-a5 =
  (j : Nat) ->
  (2021 ∣ sumCoprimePowersUpTo 2021 j)
    ↔ (Not (42 ∣ j) × Not (46 ∣ j))
