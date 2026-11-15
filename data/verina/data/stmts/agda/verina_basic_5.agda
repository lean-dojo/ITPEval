-- Statement-only formalization of VERINA corpus artifact verina_basic_5,
-- catalog title "multiply": a total integer program returns the product of
-- its two inputs and is connected to its two-difference correctness contract.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic5 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 3 _∧_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

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

intMultiply : Int → Int → Int
intMultiply (pos m) (pos n) = pos (m * n)
intMultiply (pos m) (negsuc n) = negative (m * suc n)
intMultiply (negsuc m) (pos n) = negative (suc m * n)
intMultiply (negsuc m) (negsuc n) = pos (suc m * suc n)

zeroInt : Int
zeroInt = pos zero

multiply-precond : Int → Int → Set
multiply-precond a b = Top

multiply :
  (a b : Int) →
  multiply-precond a b →
  Int
multiply a b h-precond =
  intMultiply a b

multiply-postcond :
  (a b result : Int) →
  multiply-precond a b →
  Set
multiply-postcond a b result h-precond =
  (intSubtract result (intMultiply a b) ≡ zeroInt) ∧
  (intSubtract (intMultiply a b) result ≡ zeroInt)

multiply-spec-satisfied : Set
multiply-spec-satisfied =
  (a b : Int) →
  (h-precond : multiply-precond a b) →
  multiply-postcond
    a
    b
    (multiply a b h-precond)
    h-precond
