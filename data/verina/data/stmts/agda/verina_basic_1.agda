-- Statement-only formalization of VERINA corpus artifact verina_basic_1,
-- catalog title "hasOppositeSign": a deterministic integer-product sign test
-- returns whether two integers have opposite signs and is connected to its
-- Boolean correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic1 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infixr 2 _∨_
infixr 3 _∧_

record Top : Set where
  constructor top

data Empty : Set where

Not : Set → Set
Not A = A → Empty

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

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

intMultiply : Int → Int → Int
intMultiply (pos m) (pos n) = pos (m * n)
intMultiply (pos m) (negsuc n) = negative (m * suc n)
intMultiply (negsuc m) (pos n) = negative (suc m * n)
intMultiply (negsuc m) (negsuc n) = pos (suc m * suc n)

zeroInt : Int
zeroInt = pos zero

IntLess : Int → Int → Set
IntLess x y = IsTrue (intLess x y)

hasOppositeSign-precond : Int → Int → Set
hasOppositeSign-precond a b = Top

hasOppositeSign :
  (a b : Int) →
  hasOppositeSign-precond a b →
  Bool
hasOppositeSign a b h-precond =
  intLess (intMultiply a b) zeroInt

OppositeSigns : Int → Int → Set
OppositeSigns a b =
  (IntLess a zeroInt ∧ IntLess zeroInt b) ∨
  (IntLess zeroInt a ∧ IntLess b zeroInt)

hasOppositeSign-postcond :
  (a b : Int) →
  (result : Bool) →
  hasOppositeSign-precond a b →
  Set
hasOppositeSign-postcond a b result h-precond =
  (OppositeSigns a b → IsTrue result) ∧
  (Not (OppositeSigns a b) → Not (IsTrue result))

hasOppositeSign-spec-satisfied : Set
hasOppositeSign-spec-satisfied =
  (a b : Int) →
  (h-precond : hasOppositeSign-precond a b) →
  hasOppositeSign-postcond
    a
    b
    (hasOppositeSign a b h-precond)
    h-precond
