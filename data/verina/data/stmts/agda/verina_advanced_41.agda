-- Statement-only formalization of VERINA corpus artifact verina_advanced_41,
-- catalog title "maxOfThree": a deterministic nested-comparison program
-- returns the greatest of three integers and is connected to its maximum-value
-- correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced41 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 2 _∨_
infixr 3 _∧_
infixr 5 _&&_

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

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

_&&_ : Bool → Bool → Bool
true && other = other
false && other = false

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

intGreaterOrEqual : Int → Int → Bool
intGreaterOrEqual x y = intLessOrEqual y x

IntGreaterOrEqual : Int → Int → Set
IntGreaterOrEqual x y = IsTrue (intGreaterOrEqual x y)

maxOfThree-precond : Int → Int → Int → Set
maxOfThree-precond a b c = Top

maxOfThree :
  (a b c : Int) →
  maxOfThree-precond a b c →
  Int
maxOfThree a b c h-precond =
  if intGreaterOrEqual a b && intGreaterOrEqual a c
  then a
  else
    if intGreaterOrEqual b a && intGreaterOrEqual b c
    then b
    else c

maxOfThree-postcond :
  (a b c result : Int) →
  maxOfThree-precond a b c →
  Set
maxOfThree-postcond a b c result h-precond =
  (IntGreaterOrEqual result a ∧
   IntGreaterOrEqual result b ∧
   IntGreaterOrEqual result c) ∧
  (result ≡ a ∨ result ≡ b ∨ result ≡ c)

maxOfThree-spec-satisfied : Set
maxOfThree-spec-satisfied =
  (a b c : Int) →
  (h-precond : maxOfThree-precond a b c) →
  maxOfThree-postcond
    a
    b
    c
    (maxOfThree a b c h-precond)
    h-precond
