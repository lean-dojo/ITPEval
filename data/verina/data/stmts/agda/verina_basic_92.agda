-- Statement-only formalization of VERINA corpus artifact verina_basic_92,
-- catalog title "SwapArithmetic": a deterministic integer program swaps two
-- inputs through the specified subtraction-and-addition assignments and is
-- connected to its full correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic92 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

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

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

intAdd : Int → Int → Int
intAdd (pos m) (pos n) = pos (m + n)
intAdd (pos m) (negsuc n) = difference m (suc n)
intAdd (negsuc m) (pos n) = difference n (suc m)
intAdd (negsuc m) (negsuc n) = negsuc (suc (m + n))

intNegate : Int → Int
intNegate (pos zero) = pos zero
intNegate (pos (suc n)) = negsuc n
intNegate (negsuc n) = pos (suc n)

intSubtract : Int → Int → Int
intSubtract x y = intAdd x (intNegate y)

SwapArithmetic-precond : Int → Int → Set
SwapArithmetic-precond X Y = Top

SwapArithmetic :
  (X Y : Int) →
  SwapArithmetic-precond X Y →
  Int × Int
SwapArithmetic X Y h-precond =
  let x1 = X
      y1 = Y
      x2 = intSubtract y1 x1
      y2 = intSubtract y1 x2
      x3 = intAdd y2 x2
  in x3 , y2

SwapArithmetic-postcond :
  (X Y : Int) →
  (result : Int × Int) →
  SwapArithmetic-precond X Y →
  Set
SwapArithmetic-postcond X Y result h-precond =
  (pairFirst result ≡ Y) ∧
  (pairSecond result ≡ X) ∧
  (X ≢ Y →
    (pairFirst result ≢ X) ∧
    (pairSecond result ≢ Y))

SwapArithmetic-spec-satisfied : Set
SwapArithmetic-spec-satisfied =
  (X Y : Int) →
  (h-precond : SwapArithmetic-precond X Y) →
  SwapArithmetic-postcond
    X
    Y
    (SwapArithmetic X Y h-precond)
    h-precond
