-- Statement-only formalization of VERINA corpus artifact verina_basic_59,
-- catalog title "DoubleQuadruple": a total integer program returns twice its
-- input and then twice that result, connected to its pair-valued correctness
-- contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic59 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infixr 3 _∧_
infixr 4 _×_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _×_ public

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

intMultiply : Int → Int → Int
intMultiply (pos m) (pos n) = pos (m * n)
intMultiply (pos m) (negsuc n) = negative (m * suc n)
intMultiply (negsuc m) (pos n) = negative (suc m * n)
intMultiply (negsuc m) (negsuc n) = pos (suc m * suc n)

twoInt : Int
twoInt = pos (suc (suc zero))

DoubleQuadruple-precond : Int → Set
DoubleQuadruple-precond x = Top

DoubleQuadruple :
  (x : Int) →
  DoubleQuadruple-precond x →
  Int × Int
DoubleQuadruple x h-precond =
  let a = intMultiply twoInt x
      b = intMultiply twoInt a
  in a , b

DoubleQuadruple-postcond :
  (x : Int) →
  (result : Int × Int) →
  DoubleQuadruple-precond x →
  Set
DoubleQuadruple-postcond x result h-precond =
  (fst result ≡ intMultiply twoInt x) ∧
  (snd result ≡ intMultiply twoInt (fst result))

DoubleQuadruple-spec-satisfied : Set
DoubleQuadruple-spec-satisfied =
  (x : Int) →
  (h-precond : DoubleQuadruple-precond x) →
  DoubleQuadruple-postcond
    x
    (DoubleQuadruple x h-precond)
    h-precond
