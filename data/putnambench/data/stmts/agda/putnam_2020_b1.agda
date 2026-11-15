-- Statement-only formalization of PutnamBench corpus artifact putnam_2020_b1
-- (putnambench__agda__putnam_2020_b1): the binary-digit-sum signed sum of
-- cubes from 1 through 2020 has remainder 1990 modulo 2020. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module Putnam2020B1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

two : Nat
two =
  suc (suc zero)

data BinaryDigitSum : Nat -> Nat -> Set where
  zero-digits :
    BinaryDigitSum zero zero
  even-digits :
    {n total : Nat} ->
    BinaryDigitSum n total ->
    BinaryDigitSum (two * n) total
  odd-digits :
    {n total : Nat} ->
    BinaryDigitSum n total ->
    BinaryDigitSum (suc (two * n)) (suc total)

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

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

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

oneInt : Int
oneInt =
  pos (suc zero)

negativeOne : Int
negativeOne =
  negsuc zero

powerInt : Int -> Nat -> Int
powerInt base zero =
  oneInt
powerInt base (suc exponent) =
  multiplyInt base (powerInt base exponent)

cubeInt : Nat -> Int
cubeInt n =
  multiplyInt (pos n)
    (multiplyInt (pos n) (pos n))

signedCube : (Nat -> Nat) -> Nat -> Int
signedCube d k =
  multiplyInt
    (powerInt negativeOne (d k))
    (cubeInt k)

sumPositiveThrough :
  Nat ->
  (Nat -> Int) ->
  Int
sumPositiveThrough zero term =
  pos zero
sumPositiveThrough (suc bound) term =
  addInt
    (sumPositiveThrough bound term)
    (term (suc bound))

record IntModEq
  (modulus : Nat)
  (left-value right-value : Int) :
  Set where

  field
    multiple : Int
    equation :
      left-value ==
      addInt right-value
        (multiplyInt (pos modulus) multiple)

putnam-2020-b1 : Set
putnam-2020-b1 =
  (d : Nat -> Nat) ->
  (S : Int) ->
  ((n : Nat) -> BinaryDigitSum n (d n)) ->
  S == sumPositiveThrough 2020 (signedCube d) ->
  IntModEq 2020 S (pos 1990)
