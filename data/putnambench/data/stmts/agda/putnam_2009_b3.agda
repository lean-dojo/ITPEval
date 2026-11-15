-- Statement-only formalization of PutnamBench corpus artifact putnam_2009_b3
-- (putnambench__agda__putnam_2009_b3): the positive indices where the
-- second difference of the number of subsets closed under integral averages
-- equals one are exactly the Mersenne numbers. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2009B3 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_ _<=Z_
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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data _<=Z_ : Int -> Int -> Set where
  negative<=positive :
    {m n : Nat} ->
    negsuc m <=Z pos n
  positive<=positive :
    {m n : Nat} ->
    m <=N n ->
    pos m <=Z pos n
  negative<=negative :
    {m n : Nat} ->
    n <=N m ->
    negsuc m <=Z negsuc n

data PositiveNat : Nat -> Set where
  positiveNat : {n : Nat} -> PositiveNat (suc n)

data PositiveInt : Int -> Set where
  positiveInt : {n : Nat} -> PositiveInt (pos (suc n))

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

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

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

oneZ : Int
oneZ =
  pos oneN

twoZ : Int
twoZ =
  pos twoN

powerOfTwo : Nat -> Nat
powerOfTwo zero =
  oneN
powerOfTwo (suc n) =
  twoN * powerOfTwo n

predecessor : Nat -> Nat
predecessor zero =
  zero
predecessor (suc n) =
  n

Subset : Set1
Subset =
  Int -> Set

SameSubset : Subset -> Subset -> Set
SameSubset left right =
  (x : Int) ->
  Iff (left x) (right x)

InInterval : Int -> Int -> Set
InInterval upper x =
  oneZ <=Z x
  and
  x <=Z upper

SubsetOfInterval : Int -> Subset -> Set
SubsetOfInterval upper S =
  (x : Int) ->
  S x ->
  InInterval upper x

ClosedUnderIntegralAverages : Subset -> Set
ClosedUnderIntegralAverages S =
  (a b : Int) ->
  S a ->
  S b ->
  (average : Int) ->
  addInt a b == addInt average average ->
  S average

Mediocre : Int -> Subset -> Set
Mediocre n S =
  SubsetOfInterval n S
  and
  ClosedUnderIntegralAverages S

record FamilyHasCardinality
  (member : Subset -> Set)
  (cardinality : Nat) :
  Set1 where

  field
    enumerate :
      Fin cardinality ->
      Subset
    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)
    enumeration-complete :
      (S : Subset) ->
      member S ->
      Exists (Fin cardinality)
        (\ index ->
          SameSubset S (enumerate index))
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      SameSubset
        (enumerate left-index)
        (enumerate right-index) ->
      left-index == right-index

record CountedBy
  (member : Subset -> Set)
  (count : Int) :
  Set1 where

  field
    magnitude :
      Nat
    count-is-magnitude :
      count == pos magnitude
    has-cardinality :
      FamilyHasCardinality member magnitude

CountsMediocreSubsets : (Int -> Int) -> Set1
CountsMediocreSubsets A =
  (n : Int) ->
  CountedBy (Mediocre n) (A n)

secondDifference : (Int -> Int) -> Int -> Int
secondDifference A n =
  addInt
    (addInt
      (A (addInt n twoZ))
      (negateInt
        (multiplyInt
          twoZ
          (A (addInt n oneZ)))))
    (A n)

QualifyingIndex : (Int -> Int) -> Int -> Set
QualifyingIndex A n =
  PositiveInt n
  and
  secondDifference A n == oneZ

MersenneNumber : Int -> Set
MersenneNumber n =
  Exists Nat
    (\ exponent ->
      PositiveNat exponent
      and
      n == pos (predecessor (powerOfTwo exponent)))

SameIntegerSet :
  (Int -> Set) ->
  (Int -> Set) ->
  Set
SameIntegerSet left right =
  (n : Int) ->
  Iff (left n) (right n)

putnam-2009-b3 : Set1
putnam-2009-b3 =
  (A : Int -> Int) ->
  CountsMediocreSubsets A ->
  SameIntegerSet
    (QualifyingIndex A)
    MersenneNumber
