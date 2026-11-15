-- Statement-only formalization of VERINA corpus artifact verina_advanced_23,
-- catalog title "isPowerOfTwo": a deterministic integer program uses
-- fuel-bounded repeated halving to decide whether its input is a positive
-- power of two. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced23 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; div-helper; mod-helper)

infixr 3 _∧_

data Empty : Set where

Not : Set → Set
Not A = A → Empty

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data Exists (P : Nat → Set) : Set where
  witness : (x : Nat) → P x → Exists P

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

two : Nat
two = suc one

oneInt : Int
oneInt = pos one

twoInt : Int
twoInt = pos two

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

intMultiply : Int → Int → Int
intMultiply (pos m) (pos n) = pos (m * n)
intMultiply (pos m) (negsuc n) = negative (m * suc n)
intMultiply (negsuc m) (pos n) = negative (suc m * n)
intMultiply (negsuc m) (negsuc n) = pos (suc m * suc n)

isPowerOfTwo-precond : Int → Set
isPowerOfTwo-precond n = Top

isPowerOfTwo-aux : Nat → Nat → Bool
isPowerOfTwo-aux current zero = false
isPowerOfTwo-aux current (suc fuel) =
  if natEqual current one
  then true
  else
    if natEqual (naturalMod current two) zero
    then isPowerOfTwo-aux (naturalDiv current two) fuel
    else false

isPowerOfTwo :
  (n : Int) →
  isPowerOfTwo-precond n →
  Bool
isPowerOfTwo (pos zero) h-precond = false
isPowerOfTwo (pos (suc magnitude)) h-precond =
  isPowerOfTwo-aux (suc magnitude) (suc magnitude)
isPowerOfTwo (negsuc magnitude) h-precond = false

pow : Int → Nat → Int
pow base zero = oneInt
pow base (suc exponent) = intMultiply base (pow base exponent)

data Positive : Int → Set where
  positive : {magnitude : Nat} → Positive (pos (suc magnitude))

isPowerOfTwo-postcond :
  (n : Int) →
  (result : Bool) →
  isPowerOfTwo-precond n →
  Set
isPowerOfTwo-postcond n true h-precond =
  Exists (λ exponent → (pow twoInt exponent ≡ n) ∧ Positive n)
isPowerOfTwo-postcond n false h-precond =
  Not (Exists (λ exponent → (pow twoInt exponent ≡ n) ∧ Positive n))

isPowerOfTwo-spec-satisfied : Set
isPowerOfTwo-spec-satisfied =
  (n : Int) →
  (h-precond : isPowerOfTwo-precond n) →
  isPowerOfTwo-postcond
    n
    (isPowerOfTwo n h-precond)
    h-precond
