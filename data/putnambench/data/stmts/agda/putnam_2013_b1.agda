-- Statement-only formalization of PutnamBench corpus artifact putnam_2013_b1
-- (putnambench__agda__putnam_2013_b1): the integer sequence defined by the
-- stated even and odd recurrences has sum c(n)c(n+2), for n from 1 through
-- 2013, equal to -1. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2013B1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

data Positive : Nat -> Set where
  positive : (n : Nat) -> Positive (suc n)

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

powerInt : Int -> Nat -> Int
powerInt base zero =
  pos one
powerInt base (suc exponent) =
  multiplyInt base (powerInt base exponent)

sumFromOneThroughInt : Nat -> (Nat -> Int) -> Int
sumFromOneThroughInt zero term =
  pos zero
sumFromOneThroughInt (suc n) term =
  addInt
    (sumFromOneThroughInt n term)
    (term (suc n))

putnam-2013-b1 : Set
putnam-2013-b1 =
  (c : Nat -> Int) ->
  c one == pos one ->
  ((n : Nat) ->
    Positive n ->
    c (two * n) == c n) ->
  ((n : Nat) ->
    Positive n ->
    c (two * n + one) ==
    multiplyInt
      (powerInt (negsuc zero) n)
      (c n)) ->
  sumFromOneThroughInt 2013
    (\ n ->
      multiplyInt
        (c n)
        (c (n + two)))
  ==
  negsuc zero
