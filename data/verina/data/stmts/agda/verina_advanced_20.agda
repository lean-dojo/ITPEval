-- Statement-only formalization of VERINA corpus artifact verina_advanced_20,
-- catalog title "isItEight": a deterministic integer program decides whether
-- its input is divisible by eight or has eight as a decimal digit.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced20 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; div-helper; mod-helper)

infixr 2 _↔_
infixr 3 _∨_
infixr 5 _||_

record Top : Set where
  constructor top

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward : A → B
    backward : B → A

data Exists (P : Nat → Set) : Set where
  witness : (i : Nat) → P i → Exists P

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

_||_ : Bool → Bool → Bool
true || other = true
false || other = other

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

eight : Nat
eight =
  suc (suc (suc (suc (suc (suc (suc (suc zero)))))))

ten : Nat
ten = suc (suc eight)

power : Nat → Nat → Nat
power base zero = one
power base (suc exponent) = base * power base exponent

intNatAbs : Int → Nat
intNatAbs (pos magnitude) = magnitude
intNatAbs (negsuc magnitude) = suc magnitude

isItEight-precond : Int → Set
isItEight-precond n = Top

hasDigitEightWithFuel : Nat → Nat → Bool
hasDigitEightWithFuel zero current = false
hasDigitEightWithFuel (suc fuel) zero = false
hasDigitEightWithFuel (suc fuel) current@(suc _) =
  if natEqual (naturalMod current ten) eight
  then true
  else
    hasDigitEightWithFuel
      fuel
      (naturalDiv current ten)

hasDigitEight : Nat → Bool
hasDigitEight magnitude =
  hasDigitEightWithFuel magnitude magnitude

divisibleByEight : Int → Bool
divisibleByEight n =
  natEqual (naturalMod (intNatAbs n) eight) zero

isItEight :
  (n : Int) →
  isItEight-precond n →
  Bool
isItEight n h-precond =
  divisibleByEight n || hasDigitEight (intNatAbs n)

decimalDigitAt : Nat → Nat → Nat
decimalDigitAt magnitude position =
  naturalMod
    (naturalDiv magnitude (power ten position))
    ten

ContainsDigitEight : Nat → Set
ContainsDigitEight magnitude =
  Exists (λ position → decimalDigitAt magnitude position ≡ eight)

isItEight-postcond :
  (n : Int) →
  (result : Bool) →
  isItEight-precond n →
  Set
isItEight-postcond n result h-precond =
  (IsTrue (divisibleByEight n) ∨
   ContainsDigitEight (intNatAbs n))
  ↔ IsTrue result

isItEight-spec-satisfied : Set
isItEight-spec-satisfied =
  (n : Int) →
  (h-precond : isItEight-precond n) →
  isItEight-postcond
    n
    (isItEight n h-precond)
    h-precond
