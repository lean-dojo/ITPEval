-- Statement-only formalization of VERINA corpus artifact verina_advanced_7,
-- catalog title "binaryToDecimal": a deterministic recursive program converts
-- a big-endian list of binary natural-number digits to its decimal value and is
-- connected to its fold-based correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced7 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 2 _∨_
infixr 3 _∧_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

one : Nat
one = suc zero

two : Nat
two = suc one

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

power : Nat → Nat → Nat
power base zero = one
power base (suc exponent) = power base exponent * base

AllBinaryDigits : List Nat → Set
AllBinaryDigits [] = Top
AllBinaryDigits (digit ∷ digits) =
  ((digit ≡ zero) ∨ (digit ≡ one)) ∧ AllBinaryDigits digits

binaryToDecimal-precond : List Nat → Set
binaryToDecimal-precond digits = AllBinaryDigits digits

binaryToDecimal-helper : List Nat → Nat
binaryToDecimal-helper [] = zero
binaryToDecimal-helper (first ∷ rest) =
  first * power two (listLength rest) +
  binaryToDecimal-helper rest

binaryToDecimal :
  (digits : List Nat) →
  binaryToDecimal-precond digits →
  Nat
binaryToDecimal digits h-precond =
  binaryToDecimal-helper digits

foldLeft : {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

binaryFold : List Nat → Nat
binaryFold digits =
  foldLeft
    (λ accumulator bit → accumulator * two + bit)
    zero
    digits

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

binaryToDecimal-postcond :
  (digits : List Nat) →
  (result : Nat) →
  binaryToDecimal-precond digits →
  Set
binaryToDecimal-postcond digits result h-precond =
  (natSubtract result (binaryFold digits) ≡ zero) ∧
  (natSubtract (binaryFold digits) result ≡ zero)

binaryToDecimal-spec-satisfied : Set
binaryToDecimal-spec-satisfied =
  (digits : List Nat) →
  (h-precond : binaryToDecimal-precond digits) →
  binaryToDecimal-postcond
    digits
    (binaryToDecimal digits h-precond)
    h-precond
