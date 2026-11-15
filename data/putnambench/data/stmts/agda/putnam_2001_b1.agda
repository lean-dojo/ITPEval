-- Statement-only formalization of PutnamBench corpus artifact putnam_2001_b1
-- (putnambench__agda__putnam_2001_b1): equality of the red- and black-square
-- sums in an evenly colored row-major numbered grid. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

data Even : Nat -> Set where
  even-zero : Even zero
  even-step : {n : Nat} -> Even n -> Even (suc (suc n))

half : Nat -> Nat
half zero =
  zero
half (suc zero) =
  zero
half (suc (suc n)) =
  suc (half n)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

finToNat : {n : Nat} -> Fin n -> Nat
finToNat fzero =
  zero
finToNat (fsuc i) =
  suc (finToNat i)

data Color : Set where
  red   : Color
  black : Color

redCount : Color -> Nat
redCount red =
  suc zero
redCount black =
  zero

redContribution : Color -> Int -> Int
redContribution red value =
  value
redContribution black value =
  pos zero

blackContribution : Color -> Int -> Int
blackContribution red value =
  pos zero
blackContribution black value =
  value

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

sumFinNat : {n : Nat} -> (Fin n -> Nat) -> Nat
sumFinNat {zero} terms =
  zero
sumFinNat {suc n} terms =
  terms fzero + sumFinNat (\ i -> terms (fsuc i))

sumFinInt : {n : Nat} -> (Fin n -> Int) -> Int
sumFinInt {zero} terms =
  pos zero
sumFinInt {suc n} terms =
  addInt
    (terms fzero)
    (sumFinInt (\ i -> terms (fsuc i)))

putnam-2001-b1 : Set
putnam-2001-b1 =
  (n : Nat) ->
  Positive n ->
  Even n ->
  (nums : Fin n -> Fin n -> Int) ->
  (colors : Fin n -> Fin n -> Color) ->
  ((k l : Fin n) ->
    nums k l ==
    pos (suc (finToNat k * n + finToNat l))) ->
  ((k : Fin n) ->
    sumFinNat (\ l -> redCount (colors k l)) ==
    half n) ->
  ((l : Fin n) ->
    sumFinNat (\ k -> redCount (colors k l)) ==
    half n) ->
  sumFinInt
    (\ k ->
      sumFinInt
        (\ l ->
          redContribution
            (colors k l)
            (nums k l)))
  ==
  sumFinInt
    (\ k ->
      sumFinInt
        (\ l ->
          blackContribution
            (colors k l)
            (nums k l)))
