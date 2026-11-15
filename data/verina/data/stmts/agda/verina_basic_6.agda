-- Statement-only formalization of VERINA corpus artifact verina_basic_6,
-- catalog title "minOfThree": a deterministic integer program returns the
-- minimum of three inputs and is connected to its lower-bound and input-choice
-- correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic6 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc)

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

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

boolAnd : Bool → Bool → Bool
boolAnd true other = other
boolAnd false other = false

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero n = true
natLessOrEqual (suc m) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos m) (negsuc n) = false
intLessOrEqual (negsuc m) (pos n) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

IntLessOrEqual : Int → Int → Set
IntLessOrEqual x y = IsTrue (intLessOrEqual x y)

minOfThree-precond : Int → Int → Int → Set
minOfThree-precond a b c = Top

minOfThree :
  (a b c : Int) →
  minOfThree-precond a b c →
  Int
minOfThree a b c h-precond =
  if boolAnd (intLessOrEqual a b) (intLessOrEqual a c)
  then a
  else
    if boolAnd (intLessOrEqual b a) (intLessOrEqual b c)
    then b
    else c

minOfThree-postcond :
  (a b c result : Int) →
  minOfThree-precond a b c →
  Set
minOfThree-postcond a b c result h-precond =
  (IntLessOrEqual result a ∧
    (IntLessOrEqual result b ∧ IntLessOrEqual result c)) ∧
  ((result ≡ a) ∨ ((result ≡ b) ∨ (result ≡ c)))

minOfThree-spec-satisfied : Set
minOfThree-spec-satisfied =
  (a b c : Int) →
  (h-precond : minOfThree-precond a b c) →
  minOfThree-postcond
    a
    b
    c
    (minOfThree a b c h-precond)
    h-precond
