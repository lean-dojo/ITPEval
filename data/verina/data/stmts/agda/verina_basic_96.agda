-- Statement-only formalization of VERINA corpus artifact verina_basic_96,
-- catalog title "SwapSimultaneous": a deterministic integer-pair program
-- simultaneously returns its two inputs in reversed order and is connected
-- to its full correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic96 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int)

infixr 3 _∧_
infixr 4 _,_
infixr 5 _×_
infix 4 _≢_

record Top : Set where
  constructor top

data Bottom : Set where

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first-conjunct : A
    second-conjunct : B

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    pairFirst : A
    pairSecond : B

open _×_ public

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → Bottom

SwapSimultaneous-precond : Int → Int → Set
SwapSimultaneous-precond X Y = Top

SwapSimultaneous :
  (X Y : Int) →
  SwapSimultaneous-precond X Y →
  Int × Int
SwapSimultaneous X Y h-precond =
  Y , X

SwapSimultaneous-postcond :
  (X Y : Int) →
  (result : Int × Int) →
  SwapSimultaneous-precond X Y →
  Set
SwapSimultaneous-postcond X Y result h-precond =
  (pairFirst result ≡ Y) ∧
  (pairSecond result ≡ X) ∧
  (X ≢ Y →
    (pairFirst result ≢ X) ∧
    (pairSecond result ≢ Y))

SwapSimultaneous-spec-satisfied : Set
SwapSimultaneous-spec-satisfied =
  (X Y : Int) →
  (h-precond : SwapSimultaneous-precond X Y) →
  SwapSimultaneous-postcond
    X
    Y
    (SwapSimultaneous X Y h-precond)
    h-precond
