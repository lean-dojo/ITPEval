-- Statement-only formalization of PutnamBench corpus artifact putnam_2013_a6
-- (putnambench__agda__putnam_2013_a6): positivity of the specified
-- integer-kernel double sum over every nonempty finite subset of Int x Int.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record Point : Set where
  constructor point
  field
    x-coordinate : Int
    y-coordinate : Int

open Point

Injective : {A B : Set} -> (A -> B) -> Set
Injective {A} f =
  (i j : A) ->
  f i == f j ->
  i == j

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

fourN : Nat
fourN =
  suc threeN

twelveN : Nat
twelveN =
  fourN + fourN + fourN

zeroZ : Int
zeroZ =
  pos zero

minusOneZ : Int
minusOneZ =
  negsuc zero

minusTwoZ : Int
minusTwoZ =
  negsuc oneN

minusFourZ : Int
minusFourZ =
  negsuc threeN

twoZ : Int
twoZ =
  pos twoN

fourZ : Int
fourZ =
  pos fourN

twelveZ : Int
twelveZ =
  pos twelveN

negativeNat : Nat -> Int
negativeNat zero =
  zeroZ
negativeNat (suc n) =
  negsuc n

differenceNat : Nat -> Nat -> Int
differenceNat zero zero =
  zeroZ
differenceNat (suc m) zero =
  pos (suc m)
differenceNat zero (suc n) =
  negsuc n
differenceNat (suc m) (suc n) =
  differenceNat m n

negateInt : Int -> Int
negateInt (pos n) =
  negativeNat n
negateInt (negsuc n) =
  pos (suc n)

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  differenceNat m (suc n)
addInt (negsuc m) (pos n) =
  differenceNat n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

subtractInt : Int -> Int -> Int
subtractInt x y =
  addInt x (negateInt y)

sumFinInt : {n : Nat} -> (Fin n -> Int) -> Int
sumFinInt {zero} terms =
  zeroZ
sumFinInt {suc n} terms =
  addInt
    (terms fzero)
    (sumFinInt (\ i -> terms (fsuc i)))

kernel : Int -> Int -> Int
kernel (negsuc (suc zero)) (negsuc (suc zero)) = minusOneZ
kernel (negsuc (suc zero)) (negsuc zero)       = minusTwoZ
kernel (negsuc (suc zero)) (pos zero)          = twoZ
kernel (negsuc (suc zero)) (pos (suc zero))    = minusTwoZ
kernel (negsuc (suc zero)) (pos (suc (suc zero))) = minusOneZ

kernel (negsuc zero) (negsuc (suc zero))       = minusTwoZ
kernel (negsuc zero) (negsuc zero)             = fourZ
kernel (negsuc zero) (pos zero)                = minusFourZ
kernel (negsuc zero) (pos (suc zero))          = fourZ
kernel (negsuc zero) (pos (suc (suc zero)))    = minusTwoZ

kernel (pos zero) (negsuc (suc zero))          = twoZ
kernel (pos zero) (negsuc zero)                = minusFourZ
kernel (pos zero) (pos zero)                   = twelveZ
kernel (pos zero) (pos (suc zero))             = minusFourZ
kernel (pos zero) (pos (suc (suc zero)))       = twoZ

kernel (pos (suc zero)) (negsuc (suc zero))    = minusTwoZ
kernel (pos (suc zero)) (negsuc zero)          = fourZ
kernel (pos (suc zero)) (pos zero)             = minusFourZ
kernel (pos (suc zero)) (pos (suc zero))       = fourZ
kernel (pos (suc zero)) (pos (suc (suc zero))) = minusTwoZ

kernel (pos (suc (suc zero))) (negsuc (suc zero)) = minusOneZ
kernel (pos (suc (suc zero))) (negsuc zero)       = minusTwoZ
kernel (pos (suc (suc zero))) (pos zero)          = twoZ
kernel (pos (suc (suc zero))) (pos (suc zero))    = minusTwoZ
kernel (pos (suc (suc zero))) (pos (suc (suc zero))) = minusOneZ

kernel _ _ =
  zeroZ

energy :
  {n : Nat} ->
  (Fin n -> Point) ->
  Int
energy points =
  sumFinInt
    (\ i ->
      sumFinInt
        (\ j ->
          kernel
            (subtractInt
              (x-coordinate (points i))
              (x-coordinate (points j)))
            (subtractInt
              (y-coordinate (points i))
              (y-coordinate (points j)))))

data PositiveInteger : Int -> Set where
  positive : {n : Nat} -> PositiveInteger (pos (suc n))

putnam-2013-a6 : Set
putnam-2013-a6 =
  (n : Nat) ->
  (points : Fin (suc n) -> Point) ->
  Injective points ->
  PositiveInteger (energy points)
