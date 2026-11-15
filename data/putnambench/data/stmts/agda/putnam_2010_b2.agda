-- Statement-only formalization of PutnamBench corpus artifact putnam_2010_b2
-- (putnambench__agda__putnam_2010_b2): the least possible side length of a
-- noncollinear integer-coordinate triangle whose three side lengths are
-- integers is 3. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2010B2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

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

squareInt : Int -> Int
squareInt x =
  multiplyInt x x

record Point : Set where
  constructor point
  field
    x-coordinate : Int
    y-coordinate : Int

open Point

squaredDistance : Point -> Point -> Int
squaredDistance p q =
  addInt
    (squareInt
      (subtractInt (x-coordinate p) (x-coordinate q)))
    (squareInt
      (subtractInt (y-coordinate p) (y-coordinate q)))

HasDistance : Point -> Point -> Nat -> Set
HasDistance p q n =
  squaredDistance p q == pos (n * n)

Noncollinear : Point -> Point -> Point -> Set
Noncollinear a b c =
  multiplyInt
    (subtractInt (x-coordinate b) (x-coordinate a))
    (subtractInt (y-coordinate c) (y-coordinate a))
  !=
  multiplyInt
    (subtractInt (y-coordinate b) (y-coordinate a))
    (subtractInt (x-coordinate c) (x-coordinate a))

record ValidTriangleWithAB (ab : Nat) : Set where
  field
    A B C : Point
    ac bc : Nat
    noncollinear : Noncollinear A B C
    ab-distance : HasDistance A B ab
    ac-distance : HasDistance A C ac
    bc-distance : HasDistance B C bc

record IsLeast (P : Nat -> Set) (n : Nat) : Set where
  field
    member      : P n
    lower-bound : (m : Nat) -> P m -> n <=N m

three : Nat
three =
  suc (suc (suc zero))

putnam-2010-b2 : Set
putnam-2010-b2 =
  IsLeast ValidTriangleWithAB three
