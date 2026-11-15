-- Statement-only formalization of VERINA corpus artifact verina_basic_76,
-- catalog title "myMin": a deterministic comparison returns the minimum of
-- two integers and is connected to its branchwise correctness contract.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic76 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_

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

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) =
  natLessOrEqual n m

IntLess : Int → Int → Set
IntLess x y = IsTrue (intLess x y)

IntLessOrEqual : Int → Int → Set
IntLessOrEqual x y = IsTrue (intLessOrEqual x y)

myMin-precond : Int → Int → Set
myMin-precond x y = Top

myMin :
  (x y : Int) →
  myMin-precond x y →
  Int
myMin x y h-precond =
  if intLess x y then x else y

myMin-postcond :
  (x y result : Int) →
  myMin-precond x y →
  Set
myMin-postcond x y result h-precond =
  (IntLessOrEqual x y → result ≡ x) ∧
  (IntLess y x → result ≡ y)

myMin-spec-satisfied : Set
myMin-spec-satisfied =
  (x y : Int) →
  (h-precond : myMin-precond x y) →
  myMin-postcond
    x
    y
    (myMin x y h-precond)
    h-precond
