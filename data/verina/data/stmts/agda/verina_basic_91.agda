-- Statement-only formalization of VERINA corpus artifact verina_basic_91,
-- catalog title "Swap": a deterministic integer-pair program exchanges its
-- two inputs and is connected to its full correctness contract. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic91 where

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

Swap-precond : Int → Int → Set
Swap-precond X Y = Top

Swap :
  (X Y : Int) →
  Swap-precond X Y →
  Int × Int
Swap X Y h-precond =
  let x = X
      y = Y
      tmp = x
      new-x = y
      new-y = tmp
  in new-x , new-y

Swap-postcond :
  (X Y : Int) →
  (result : Int × Int) →
  Swap-precond X Y →
  Set
Swap-postcond X Y result h-precond =
  (pairFirst result ≡ Y) ∧
  (pairSecond result ≡ X) ∧
  (X ≢ Y →
    (pairFirst result ≢ X) ∧
    (pairSecond result ≢ Y))

Swap-spec-satisfied : Set
Swap-spec-satisfied =
  (X Y : Int) →
  (h-precond : Swap-precond X Y) →
  Swap-postcond
    X
    Y
    (Swap X Y h-precond)
    h-precond
