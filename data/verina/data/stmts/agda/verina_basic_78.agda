-- Statement-only formalization of VERINA corpus artifact verina_basic_78,
-- catalog title "MultipleReturns": a deterministic integer program returns
-- the sum and difference of two arbitrary integers as a pair and is connected
-- to its componentwise correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic78 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 3 _∧_
infixr 4 _,_
infixr 5 _×_
infixl 6 _+z_ _-z_

record Top : Set where
  constructor top

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

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

_+z_ : Int → Int → Int
pos m +z pos n = pos (m + n)
pos m +z negsuc n = difference m (suc n)
negsuc m +z pos n = difference n (suc m)
negsuc m +z negsuc n = negsuc (suc (m + n))

negateInt : Int → Int
negateInt (pos zero) = pos zero
negateInt (pos (suc n)) = negsuc n
negateInt (negsuc n) = pos (suc n)

_-z_ : Int → Int → Int
x -z y = x +z negateInt y

MultipleReturns-precond : Int → Int → Set
MultipleReturns-precond x y = Top

MultipleReturns :
  (x y : Int) →
  MultipleReturns-precond x y →
  Int × Int
MultipleReturns x y h-precond =
  let more = x +z y
      less = x -z y
  in more , less

MultipleReturns-postcond :
  (x y : Int) →
  (result : Int × Int) →
  MultipleReturns-precond x y →
  Set
MultipleReturns-postcond x y result h-precond =
  (pairFirst result ≡ x +z y) ∧
  (pairSecond result +z y ≡ x)

MultipleReturns-spec-satisfied : Set
MultipleReturns-spec-satisfied =
  (x y : Int) →
  (h-precond : MultipleReturns-precond x y) →
  MultipleReturns-postcond
    x
    y
    (MultipleReturns x y h-precond)
    h-precond
