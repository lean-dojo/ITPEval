-- Statement-only formalization of VERINA corpus artifact verina_basic_8,
-- catalog title "myMin": a deterministic comparison returns the minimum of
-- two integers and is connected to its lower-bound-and-input-choice
-- correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic8 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 2 _∨_
infixr 3 _∧_

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) =
  natLessOrEqual n m

IntLessOrEqual : Int → Int → Set
IntLessOrEqual x y = IsTrue (intLessOrEqual x y)

myMin-precond : Int → Int → Set
myMin-precond a b = Top

myMin :
  (a b : Int) →
  myMin-precond a b →
  Int
myMin a b h-precond =
  if intLessOrEqual a b then a else b

myMin-postcond :
  (a b result : Int) →
  myMin-precond a b →
  Set
myMin-postcond a b result h-precond =
  (IntLessOrEqual result a ∧ IntLessOrEqual result b) ∧
  (result ≡ a ∨ result ≡ b)

myMin-spec-satisfied : Set
myMin-spec-satisfied =
  (a b : Int) →
  (h-precond : myMin-precond a b) →
  myMin-postcond
    a
    b
    (myMin a b h-precond)
    h-precond
