-- Statement-only formalization of PutnamBench corpus artifact putnam_1965_b3:
-- exactly three positive integer right-triangle side triples with ordered legs
-- have area equal to twice their perimeter. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_
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
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

data IntLessOrEqual : Int -> Int -> Set where
  positive<=positive :
    {m n : Nat} ->
    m <=N n ->
    IntLessOrEqual (pos m) (pos n)
  negative<=positive :
    {m n : Nat} ->
    IntLessOrEqual (negsuc m) (pos n)
  negative<=negative :
    {m n : Nat} ->
    n <=N m ->
    IntLessOrEqual (negsuc m) (negsuc n)

data Positive : Int -> Set where
  positive :
    {n : Nat} ->
    Positive (pos (suc n))

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

squareInt : Int -> Int
squareInt x =
  multiplyInt x x

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

fourZ : Int
fourZ =
  pos (suc three)

record Triple : Set where
  constructor triple
  field
    first-coordinate  : Int
    second-coordinate : Int
    third-coordinate  : Int

open Triple

TriangleSolution : Triple -> Set
TriangleSolution sides =
  Positive (first-coordinate sides)
  and
  IntLessOrEqual
    (first-coordinate sides)
    (second-coordinate sides)
  and
  Positive (third-coordinate sides)
  and
  addInt
    (squareInt (first-coordinate sides))
    (squareInt (second-coordinate sides))
  ==
  squareInt (third-coordinate sides)
  and
  multiplyInt
    (first-coordinate sides)
    (second-coordinate sides)
  ==
  multiplyInt fourZ
    (addInt
      (addInt
        (first-coordinate sides)
        (second-coordinate sides))
      (third-coordinate sides))

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record HasCardinality
  {A : Set}
  (P : A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      P (enumerate index)
    enumeration-complete :
      (item : A) ->
      P item ->
      Exists (Fin cardinality)
        (\ index -> item == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

putnam-1965-b3 : Set
putnam-1965-b3 =
  HasCardinality TriangleSolution three
