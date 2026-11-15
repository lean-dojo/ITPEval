-- Statement-only formalization of VERINA corpus artifact verina_advanced_14,
-- catalog title "ifPowerOfFour": a deterministic natural-number program
-- decides whether its input is an exact power of four. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced14 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; div-helper; mod-helper)

infix 2 _↔_

record Top : Set where
  constructor top

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward : A → B
    backward : B → A

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

naturalDiv : Nat → Nat → Nat
naturalDiv numerator zero = zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

one : Nat
one = suc zero

four : Nat
four = suc (suc (suc one))

power : Nat → Nat → Nat
power base zero = one
power base (suc exponent) = base * power base exponent

ifPowerOfFour-precond : Nat → Set
ifPowerOfFour-precond n = Top

ifPowerOfFour-helper-with-fuel : Nat → Nat → Bool
ifPowerOfFour-helper-with-fuel fuel zero = false
ifPowerOfFour-helper-with-fuel fuel (suc zero) = true
ifPowerOfFour-helper-with-fuel zero (suc (suc n)) = false
ifPowerOfFour-helper-with-fuel
  (suc fuel)
  (suc (suc n)) =
  let current = suc (suc n)
  in
    if natEqual (naturalMod current four) zero
    then
      ifPowerOfFour-helper-with-fuel
        fuel
        (naturalDiv current four)
    else false

ifPowerOfFour :
  (n : Nat) →
  ifPowerOfFour-precond n →
  Bool
ifPowerOfFour n h-precond =
  ifPowerOfFour-helper-with-fuel n n

data PowerOfFour (n : Nat) : Set where
  power-of-four :
    (exponent : Nat) →
    n ≡ power four exponent →
    PowerOfFour n

ifPowerOfFour-postcond :
  (n : Nat) →
  (result : Bool) →
  ifPowerOfFour-precond n →
  Set
ifPowerOfFour-postcond n result h-precond =
  IsTrue result ↔ PowerOfFour n

ifPowerOfFour-spec-satisfied : Set
ifPowerOfFour-spec-satisfied =
  (n : Nat) →
  (h-precond : ifPowerOfFour-precond n) →
  ifPowerOfFour-postcond
    n
    (ifPowerOfFour n h-precond)
    h-precond
