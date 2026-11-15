-- Statement-only formalization of PutnamBench corpus artifact putnam_2018_b1
-- (putnambench__agda__putnam_2018_b1): integer grid points whose removal
-- permits an equal-size partition with equal vector sums. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2018B1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _!=_ _<=N_ _<=Z_
infixr 3 _and_ _and1_
infixr 2 _or_
infix 2 _iff_ _iff1_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first-proof  : A
    second-proof : B

record _and1_ (A : Set) (B : Set1) : Set1 where
  constructor both1
  field
    first-proof1  : A
    second-proof1 : B

data _or_ (A B : Set) : Set where
  in-left  : A -> A or B
  in-right : B -> A or B

record _iff_ (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record _iff1_ (A : Set1) (B : Set) : Set1 where
  constructor equivalence1
  field
    forward1  : A -> B
    backward1 : B -> A

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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

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

sumFinInt : {n : Nat} -> (Fin n -> Int) -> Int
sumFinInt {zero} terms =
  pos zero
sumFinInt {suc n} terms =
  addInt
    (terms fzero)
    (sumFinInt (\ index -> terms (fsuc index)))

record Vector : Set where
  constructor vector
  field
    first-coordinate  : Int
    second-coordinate : Int

open Vector

Grid : Vector -> Set
Grid v =
  (pos zero <=Z first-coordinate v
  and
  first-coordinate v <=Z pos 2)
  and
  (pos zero <=Z second-coordinate v
  and
  second-coordinate v <=Z pos 100)

EvenInt : Int -> Set
EvenInt integer =
  Exists Int
    (\ half -> integer == addInt half half)

Solution : Vector -> Set
Solution v =
  Exists Int
    (\ b ->
      (pos zero <=Z b
      and
      b <=Z pos 100)
      and
      EvenInt b
      and
      v == vector (pos 1) b)

record FiniteEnumeration
  (member : Vector -> Set)
  (cardinality : Nat) :
  Set where

  field
    element :
      Fin cardinality ->
      Vector

    element-member :
      (index : Fin cardinality) ->
      member (element index)

    enumeration-complete :
      (item : Vector) ->
      member item ->
      Exists (Fin cardinality)
        (\ index -> item == element index)

    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      element left-index == element right-index ->
      left-index == right-index

open FiniteEnumeration

firstSum :
  {member : Vector -> Set} ->
  {cardinality : Nat} ->
  FiniteEnumeration member cardinality ->
  Int
firstSum enumeration =
  sumFinInt
    (\ index -> first-coordinate (element enumeration index))

secondSum :
  {member : Vector -> Set} ->
  {cardinality : Nat} ->
  FiniteEnumeration member cardinality ->
  Int
secondSum enumeration =
  sumFinInt
    (\ index -> second-coordinate (element enumeration index))

record EqualPartition (omitted : Vector) : Set1 where
  field
    left-set  : Vector -> Set
    right-set : Vector -> Set

    exhaustive :
      (item : Vector) ->
      (left-set item or right-set item)
      iff
      (Grid item and item != omitted)

    disjoint :
      (item : Vector) ->
      left-set item ->
      right-set item ->
      Bottom

    common-cardinality : Nat

    left-enumeration :
      FiniteEnumeration left-set common-cardinality

    right-enumeration :
      FiniteEnumeration right-set common-cardinality

    equal-first-sums :
      firstSum left-enumeration ==
      firstSum right-enumeration

    equal-second-sums :
      secondSum left-enumeration ==
      secondSum right-enumeration

putnam-2018-b1 : Set1
putnam-2018-b1 =
  (v : Vector) ->
  (Grid v and1 EqualPartition v)
  iff1
  Solution v
