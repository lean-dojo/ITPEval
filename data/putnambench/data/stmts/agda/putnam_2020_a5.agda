-- Statement-only formalization of PutnamBench corpus artifact putnam_2020_a5
-- (putnambench__agda__putnam_2020_a5): the largest integer for which exactly
-- 2020 finite sets of positive indices have their Fibonacci numbers sum to it
-- is the 4040th Fibonacci number minus one. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2020A5 where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<=N_ _<N_ _<=Z_
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

record FiniteNatSet : Set where
  constructor finiteNatSet
  field
    membership      : Nat -> Bool
    size            : Nat
    has-cardinality :
      HasCardinality
        (\ n -> membership n == true)
        size

open FiniteNatSet
open HasCardinality

SameFiniteNatSet :
  FiniteNatSet ->
  FiniteNatSet ->
  Set
SameFiniteNatSet left right =
  (n : Nat) ->
  membership left n == membership right n

record HasExtensionalCardinality
  {A : Set}
  (member : A -> Set)
  (equivalent : A -> A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate-extensional :
      Fin cardinality ->
      A
    enumerated-member-extensional :
      (index : Fin cardinality) ->
      member (enumerate-extensional index)
    enumeration-complete-extensional :
      (item : A) ->
      member item ->
      Exists (Fin cardinality)
        (\ index ->
          equivalent item (enumerate-extensional index))
    enumeration-injective-extensional :
      (left-index right-index : Fin cardinality) ->
      equivalent
        (enumerate-extensional left-index)
        (enumerate-extensional right-index) ->
      left-index == right-index

oneN : Nat
oneN =
  suc zero

fibonacci : Nat -> Nat
fibonacci zero =
  zero
fibonacci (suc zero) =
  oneN
fibonacci (suc (suc n)) =
  fibonacci n + fibonacci (suc n)

sumFin :
  {n : Nat} ->
  (Fin n -> Nat) ->
  Nat
sumFin {zero} terms =
  zero
sumFin {suc n} terms =
  terms fzero
  + sumFin (\ index -> terms (fsuc index))

fibonacciSum : FiniteNatSet -> Nat
fibonacciSum finiteSet =
  sumFin
    (\ index ->
      fibonacci
        (enumerate (has-cardinality finiteSet) index))

AllIndicesPositive : FiniteNatSet -> Set
AllIndicesPositive finiteSet =
  (n : Nat) ->
  membership finiteSet n == true ->
  zero <N n

Represents :
  Int ->
  FiniteNatSet ->
  Set
Represents total finiteSet =
  AllIndicesPositive finiteSet
  and
  pos (fibonacciSum finiteSet) == total

RepresentationCount :
  Int ->
  Nat ->
  Set
RepresentationCount total count =
  HasExtensionalCardinality
    (Represents total)
    SameFiniteNatSet
    count

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

putnam-2020-a5-solution : Int
putnam-2020-a5-solution =
  difference (fibonacci 4040) oneN

IsGreatestInt :
  (Int -> Set) ->
  Int ->
  Set
IsGreatestInt property greatest =
  property greatest
  and
  ((n : Int) ->
    property n ->
    n <=Z greatest)

putnam-2020-a5 : Set
putnam-2020-a5 =
  IsGreatestInt
    (\ n -> RepresentationCount n 2020)
    putnam-2020-a5-solution
