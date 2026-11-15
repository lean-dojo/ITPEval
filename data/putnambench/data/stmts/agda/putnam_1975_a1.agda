-- Statement-only formalization of PutnamBench corpus artifact putnam_1975_a1:
-- the equivalence between sums of two integer triangular numbers and
-- representations of four times the integer plus one as two squares, with
-- specified forward witnesses. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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

negateInt : Int -> Int
negateInt (pos n) =
  negative n
negateInt (negsuc n) =
  pos (suc n)

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

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

fourN : Nat
fourN =
  twoN * twoN

oneZ : Int
oneZ =
  pos oneN

twoZ : Int
twoZ =
  pos twoN

fourZ : Int
fourZ =
  pos fourN

TriangularSum : Int -> Int -> Int -> Set
TriangularSum n a b =
  multiplyInt twoZ n
  ==
  addInt
    (addInt (squareInt a) a)
    (addInt (squareInt b) b)

TwoSquareRepresentation : Int -> Int -> Int -> Set
TwoSquareRepresentation n x y =
  addInt (multiplyInt fourZ n) oneZ
  ==
  addInt (squareInt x) (squareInt y)

solutionX : Int -> Int -> Int
solutionX a b =
  addInt (addInt a b) oneZ

solutionY : Int -> Int -> Int
solutionY a b =
  subtractInt a b

putnam-1975-a1 : Set
putnam-1975-a1 =
  ((n a b : Int) ->
    Iff
      (TriangularSum n a b)
      (TwoSquareRepresentation n (solutionX a b) (solutionY a b)))
  and
  ((n : Int) ->
    Exists Int
      (\ x ->
        Exists Int
          (\ y ->
            TwoSquareRepresentation n x y)) ->
    Exists Int
      (\ a ->
        Exists Int
          (\ b ->
            TriangularSum n a b)))
