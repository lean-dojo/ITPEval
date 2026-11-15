-- Statement-only formalization of PutnamBench corpus artifact putnam_2007_b1
-- (putnambench__agda__putnam_2007_b1): for an integer polynomial with
-- nonnegative coefficients and a positive nonconstant coefficient, f(n)
-- divides f(f(n) + 1) exactly when the positive integer n is 1.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 3 _and_
infix 1 _iff_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record _iff_ (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data PositiveNatural : Nat -> Set where
  positive-natural :
    {n : Nat} ->
    PositiveNatural (suc n)

data NonnegativeInteger : Int -> Set where
  nonnegative-integer :
    {n : Nat} ->
    NonnegativeInteger (pos n)

data PositiveInteger : Int -> Set where
  positive-integer :
    {n : Nat} ->
    PositiveInteger (pos (suc n))

negativeNat : Nat -> Int
negativeNat zero =
  pos zero
negativeNat (suc n) =
  negsuc n

differenceNat : Nat -> Nat -> Int
differenceNat zero zero =
  pos zero
differenceNat (suc m) zero =
  pos (suc m)
differenceNat zero (suc n) =
  negsuc n
differenceNat (suc m) (suc n) =
  differenceNat m n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  differenceNat m (suc n)
addInt (negsuc m) (pos n) =
  differenceNat n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negativeNat (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negativeNat (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

zeroZ : Int
zeroZ =
  pos zero

oneZ : Int
oneZ =
  pos (suc zero)

Polynomial : Set
Polynomial =
  List Int

coefficientAt : Polynomial -> Nat -> Int
coefficientAt [] index =
  zeroZ
coefficientAt (coefficient ∷ coefficients) zero =
  coefficient
coefficientAt (coefficient ∷ coefficients) (suc index) =
  coefficientAt coefficients index

evaluate : Polynomial -> Int -> Int
evaluate [] x =
  zeroZ
evaluate (coefficient ∷ coefficients) x =
  addInt
    coefficient
    (multiplyInt x (evaluate coefficients x))

AllCoefficientsNonnegative : Polynomial -> Set
AllCoefficientsNonnegative polynomial =
  (index : Nat) ->
  NonnegativeInteger (coefficientAt polynomial index)

HasPositiveNonconstantCoefficient : Polynomial -> Set
HasPositiveNonconstantCoefficient polynomial =
  Exists Nat
    (\ index ->
      PositiveNatural index
      and
      PositiveInteger (coefficientAt polynomial index))

record Divides (divisor dividend : Int) : Set where
  constructor division
  field
    quotient : Int
    division-equation :
      multiplyInt divisor quotient == dividend

putnam-2007-b1 : Set
putnam-2007-b1 =
  (polynomial : Polynomial) ->
  AllCoefficientsNonnegative polynomial ->
  HasPositiveNonconstantCoefficient polynomial ->
  (n : Int) ->
  PositiveInteger n ->
  Divides
    (evaluate polynomial n)
    (evaluate polynomial
      (addInt (evaluate polynomial n) oneZ))
  iff
  n == oneZ
