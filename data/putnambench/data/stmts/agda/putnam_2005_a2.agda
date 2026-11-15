-- Statement-only formalization of PutnamBench corpus artifact putnam_2005_a2
-- (putnambench__agda__putnam_2005_a2): the number of unit-step rook tours
-- through every point of an n by 3 integer grid, from (1,1) to (n,1).
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2005A2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_; _*_)

infix 4 _<=N_ _<N_
infixr 3 _and_
infixr 2 _or_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first-proof  : A
    second-proof : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record ExistsUnique (A : Set) (P : A -> Set) : Set where
  field
    unique-value    : A
    unique-property : P unique-value
    uniqueness      : (other : A) -> P other -> other == unique-value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

record Pair (A B : Set) : Set where
  constructor _,_
  field
    first  : A
    second : B

open Pair

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record HasExtensionalCardinality
  {A : Set}
  (equivalent : A -> A -> Set)
  (member : A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A

    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)

    enumeration-complete :
      (item : A) ->
      member item ->
      Exists (Fin cardinality)
        (\ index -> equivalent item (enumerate index))

    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      equivalent (enumerate left-index) (enumerate right-index) ->
      left-index == right-index

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

power : Nat -> Nat -> Nat
power base zero =
  one
power base (suc exponent) =
  power base exponent * base

Positive : Nat -> Set
Positive n =
  one <=N n

InClosedInterval : Nat -> Nat -> Nat -> Set
InClosedInterval lower upper x =
  lower <=N x and x <=N upper

Point : Set
Point =
  Pair Int Int

GridColumn : Nat -> Int -> Set
GridColumn n coordinate =
  Exists Nat
    (\ predecessor ->
      coordinate == pos (suc predecessor)
      and
      suc predecessor <=N n)

GridRow : Int -> Set
GridRow coordinate =
  coordinate == pos one
  or
  coordinate == pos two
  or
  coordinate == pos three

GridPoint : Nat -> Point -> Set
GridPoint n point =
  GridColumn n (first point)
  and
  GridRow (second point)

successorInt : Int -> Int
successorInt (pos n) =
  pos (suc n)
successorInt (negsuc zero) =
  pos zero
successorInt (negsuc (suc n)) =
  negsuc n

AdjacentIntegers : Int -> Int -> Set
AdjacentIntegers x y =
  successorInt x == y
  or
  successorInt y == x

UnitStep : Point -> Point -> Set
UnitStep left-point right-point =
  (first left-point == first right-point
  and
  AdjacentIntegers (second left-point) (second right-point))
  or
  (second left-point == second right-point
  and
  AdjacentIntegers (first left-point) (first right-point))

zeroPoint : Point
zeroPoint =
  pos zero , pos zero

RookTour : Nat -> (Nat -> Point) -> Set
RookTour n path =
  ((point : Point) ->
    GridPoint n point ->
    ExistsUnique Nat
      (\ index ->
        InClosedInterval one (three * n) index
        and
        path index == point))
  and
  ((index : Nat) ->
    InClosedInterval one (three * n - one) index ->
    UnitStep (path index) (path (suc index)))
  and
  path zero == zeroPoint
  and
  ((index : Nat) ->
    three * n <N index ->
    path index == zeroPoint)

StartsAndEndsCorrectly : Nat -> (Nat -> Point) -> Set
StartsAndEndsCorrectly n path =
  path one == (pos one , pos one)
  and
  path (three * n) == (pos n , pos one)

ValidTour : Nat -> (Nat -> Point) -> Set
ValidTour n path =
  RookTour n path
  and
  StartsAndEndsCorrectly n path

SameTour : (Nat -> Point) -> (Nat -> Point) -> Set
SameTour left-path right-path =
  (index : Nat) ->
  left-path index == right-path index

putnam-2005-a2-solution : Nat -> Nat
putnam-2005-a2-solution zero =
  zero
putnam-2005-a2-solution (suc zero) =
  zero
putnam-2005-a2-solution (suc (suc predecessor)) =
  power two predecessor

putnam-2005-a2 : Set
putnam-2005-a2 =
  (n : Nat) ->
  Positive n ->
  HasExtensionalCardinality
    SameTour
    (ValidTour n)
    (putnam-2005-a2-solution n)
