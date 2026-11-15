-- Statement-only formalization of PutnamBench corpus artifact putnam_2001_a5
-- (putnambench__agda__putnam_2001_a5): existence and uniqueness of positive
-- integers a and n satisfying a^(n+1) - (a+1)^n = 2001. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record ExistsUnique (A : Set) (P : A -> Set) : Set where
  constructor unique-witness
  field
    value      : A
    property   : P value
    uniqueness : (other : A) -> P other -> other == value

data PositiveNatural : Nat -> Set where
  positive-natural :
    {n : Nat} ->
    PositiveNatural (suc n)

data PositiveInteger : Int -> Set where
  positive-integer :
    {n : Nat} ->
    PositiveInteger (pos (suc n))

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

negateInt : Int -> Int
negateInt (pos n) =
  negative n
negateInt (negsuc n) =
  pos (suc n)

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  difference m (suc n)
addInt (negsuc m) (pos n) =
  difference n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

subtractInt : Int -> Int -> Int
subtractInt x y =
  addInt x (negateInt y)

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

oneZ : Int
oneZ =
  pos (suc zero)

naturalPower : Int -> Nat -> Int
naturalPower base zero =
  oneZ
naturalPower base (suc exponent) =
  multiplyInt base (naturalPower base exponent)

record IntegerNaturalPair : Set where
  constructor pair
  field
    integer-coordinate : Int
    natural-coordinate : Nat

open IntegerNaturalPair

SatisfiesEquation : IntegerNaturalPair -> Set
SatisfiesEquation candidate =
  subtractInt
    (naturalPower
      (integer-coordinate candidate)
      (suc (natural-coordinate candidate)))
    (naturalPower
      (addInt (integer-coordinate candidate) oneZ)
      (natural-coordinate candidate))
  ==
  pos 2001

PositiveSolution : IntegerNaturalPair -> Set
PositiveSolution candidate =
  PositiveInteger (integer-coordinate candidate)
  and
  PositiveNatural (natural-coordinate candidate)
  and
  SatisfiesEquation candidate

putnam-2001-a5 : Set
putnam-2001-a5 =
  ExistsUnique IntegerNaturalPair PositiveSolution
