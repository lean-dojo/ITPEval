-- Statement-only formalization of PutnamBench corpus artifact putnam_2006_a3
-- (putnambench__agda__putnam_2006_a3): the specified integer recurrence
-- has 2005 consecutive terms divisible by 2006. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2006A3 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_ _<N_ _<=Z_ _dividesZ_
infixl 6 _+Z_ _-Z_
infixl 7 _*Z_
infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

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

negateInt : Int -> Int
negateInt (pos n) =
  negative n
negateInt (negsuc n) =
  pos (suc n)

_+Z_ : Int -> Int -> Int
pos m +Z pos n =
  pos (m + n)
pos m +Z negsuc n =
  difference m (suc n)
negsuc m +Z pos n =
  difference n (suc m)
negsuc m +Z negsuc n =
  negsuc (suc (m + n))

_-Z_ : Int -> Int -> Int
x -Z y =
  x +Z negateInt y

_*Z_ : Int -> Int -> Int
pos m *Z pos n =
  pos (m * n)
pos m *Z negsuc n =
  negative (m * suc n)
negsuc m *Z pos n =
  negative (suc m * n)
negsuc m *Z negsuc n =
  pos (suc m * suc n)

_<=Z_ : Int -> Int -> Set
x <=Z y =
  Exists Nat
    (\ differenceMagnitude ->
      x +Z pos differenceMagnitude == y)

record _dividesZ_ (divisor dividend : Int) : Set where
  field
    quotient : Int
    division-equation :
      divisor *Z quotient == dividend

InitialValues : (Int -> Int) -> Set
InitialValues x =
  (k : Int) ->
  (pos zero <=Z k and k <=Z pos 2006) ->
  x k == k

Recurrence : (Int -> Int) -> Set
Recurrence x =
  (k : Int) ->
  pos 2006 <=Z k ->
  x (k +Z pos 1) ==
  x k +Z x (k -Z pos 2005)

ConsecutiveDivisibleTerms : (Int -> Int) -> Set
ConsecutiveDivisibleTerms x =
  Exists Nat
    (\ i ->
      Positive i
      and
      ((j : Nat) ->
        j <N 2005 ->
        pos 2006 dividesZ x (pos (i + j))))

putnam-2006-a3 : Set
putnam-2006-a3 =
  (x : Int -> Int) ->
  InitialValues x ->
  Recurrence x ->
  ConsecutiveDivisibleTerms x
