-- Statement-only formalization of PutnamBench corpus artifact putnam_2019_b1
-- (putnambench__agda__putnam_2019_b1): the number of four-point subsets of
-- the specified integer lattice set whose vertices form a square is 5n + 1.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2019B1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Primitive using (Level; _⊔_)

infix 4 _!=_ _<=N_ _<N_
infixr 3 _and_
infixr 2 _or_
infix 1 _iff_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not proposition =
  proposition -> Bottom

_!=_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x != y =
  Not (x == y)

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data _or_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> A or B
  right : B -> A or B

record _iff_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data _<N_ : Nat -> Nat -> Set where
  zero<sucN : {n : Nat} -> zero <N suc n
  suc<sucN  : {m n : Nat} -> m <N n -> suc m <N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

five : Nat
five =
  suc (suc (suc (suc one)))

powerTwo : Nat -> Nat
powerTwo zero =
  one
powerTwo (suc exponent) =
  two * powerTwo exponent

absoluteDifference : Nat -> Nat -> Nat
absoluteDifference zero n =
  n
absoluteDifference m zero =
  m
absoluteDifference (suc m) (suc n) =
  absoluteDifference m n

absoluteIntegerDifference : Int -> Int -> Nat
absoluteIntegerDifference (pos m) (pos n) =
  absoluteDifference m n
absoluteIntegerDifference (pos m) (negsuc n) =
  suc (m + n)
absoluteIntegerDifference (negsuc m) (pos n) =
  suc (m + n)
absoluteIntegerDifference (negsuc m) (negsuc n) =
  absoluteDifference m n

integerSquare : Int -> Nat
integerSquare (pos magnitude) =
  magnitude * magnitude
integerSquare (negsuc predecessor) =
  suc predecessor * suc predecessor

record Point : Set where
  constructor point
  field
    x-coordinate : Int
    y-coordinate : Int

open Point

origin : Point
origin =
  point (pos zero) (pos zero)

squaredDistance : Point -> Point -> Nat
squaredDistance leftPoint rightPoint =
  let
    xDifference =
      absoluteIntegerDifference
        (x-coordinate leftPoint)
        (x-coordinate rightPoint)
    yDifference =
      absoluteIntegerDifference
        (y-coordinate leftPoint)
        (y-coordinate rightPoint)
  in
  xDifference * xDifference + yDifference * yDifference

Pn : Nat -> Point -> Set
Pn n p =
  p == origin
  or
  Exists Nat
    (\ k ->
      k <=N n
      and
      (integerSquare (x-coordinate p) +
       integerSquare (y-coordinate p) ==
       powerTwo k))

Subset : Set1
Subset =
  Point -> Set

SameSubset : Subset -> Subset -> Set
SameSubset leftSubset rightSubset =
  (p : Point) ->
  leftSubset p iff rightSubset p

SubsetOf : Subset -> Subset -> Set
SubsetOf leftSubset rightSubset =
  (p : Point) ->
  leftSubset p ->
  rightSubset p

PairwiseDistinct : Point -> Point -> Point -> Point -> Set
PairwiseDistinct a b c d =
  a != b
  and a != c
  and a != d
  and b != c
  and b != d
  and c != d

HasExactlyVertices :
  Subset ->
  Point ->
  Point ->
  Point ->
  Point ->
  Set
HasExactlyVertices subset a b c d =
  (p : Point) ->
  subset p
  iff
  ((p == a or p == b) or (p == c or p == d))

AreCyclicSquareVertices : Point -> Point -> Point -> Point -> Set
AreCyclicSquareVertices a b c d =
  PairwiseDistinct a b c d
  and
  (zero <N squaredDistance a b)
  and
  (squaredDistance a b == squaredDistance b c)
  and
  (squaredDistance b c == squaredDistance c d)
  and
  (squaredDistance c d == squaredDistance d a)
  and
  (squaredDistance a c == squaredDistance b d)

IsFourPointSquare : Subset -> Set
IsFourPointSquare subset =
  Exists Point
    (\ a ->
      Exists Point
        (\ b ->
          Exists Point
            (\ c ->
              Exists Point
                (\ d ->
                  HasExactlyVertices subset a b c d
                  and
                  AreCyclicSquareVertices a b c d))))

QualifyingSquareSubset : Nat -> Subset -> Set
QualifyingSquareSubset n subset =
  SubsetOf subset (Pn n)
  and
  IsFourPointSquare subset

record HasSquareSubsetCardinality
  (n cardinality : Nat) :
  Set1 where

  field
    enumerate :
      Fin cardinality ->
      Subset

    enumerated-square :
      (index : Fin cardinality) ->
      QualifyingSquareSubset n (enumerate index)

    enumeration-complete :
      (subset : Subset) ->
      QualifyingSquareSubset n subset ->
      Exists (Fin cardinality)
        (\ index ->
          SameSubset subset (enumerate index))

    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      SameSubset
        (enumerate left-index)
        (enumerate right-index) ->
      left-index == right-index

putnam-2019-b1 : Set1
putnam-2019-b1 =
  (n : Nat) ->
  HasSquareSubsetCardinality n (five * n + one)
