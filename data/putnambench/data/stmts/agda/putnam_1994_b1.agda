-- Statement-only formalization of PutnamBench corpus artifact putnam_1994_b1:
-- the positive integers lying within 250 of exactly 15 natural-number
-- perfect squares are precisely two stated intervals. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1994B1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_ _<=Z_
infixr 3 _and_
infixr 2 _or_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record HasCardinality
  {A : Set}
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
        (\ index -> item == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

subtractSquare : Int -> Nat -> Int
subtractSquare (pos n) m =
  difference n (m * m)
subtractSquare (negsuc n) m =
  negsuc (n + m * m)

absoluteValue : Int -> Nat
absoluteValue (pos n) =
  n
absoluteValue (negsuc n) =
  suc n

data PositiveInteger : Int -> Set where
  positive : {n : Nat} -> PositiveInteger (pos (suc n))

Within250OfSquare : Int -> Nat -> Set
Within250OfSquare n m =
  absoluteValue (subtractSquare n m) <=N 250

ExactlyFifteenNearbySquares : Int -> Set
ExactlyFifteenNearbySquares n =
  HasCardinality (Within250OfSquare n) 15

putnam-1994-b1-solution : Int -> Set
putnam-1994-b1-solution n =
  ((pos 315 <=Z n) and (n <=Z pos 325))
  or
  ((pos 332 <=Z n) and (n <=Z pos 350))

putnam-1994-b1 : Set
putnam-1994-b1 =
  (n : Int) ->
  Iff
    (putnam-1994-b1-solution n)
    (PositiveInteger n and ExactlyFifteenNearbySquares n)
