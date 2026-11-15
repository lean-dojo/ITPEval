-- Statement-only formalization of PutnamBench corpus artifact putnam_2017_b6
-- (putnambench__agda__putnam_2017_b6): the number of ordered 64-tuples of
-- distinct integers from 1 through 2017 whose stated weighted sum is divisible
-- by 2017. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; div-helper)

infix 4 _<=N_ _divides_
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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

toNat : {n : Nat} -> Fin n -> Nat
toNat fzero =
  zero
toNat (fsuc index) =
  suc (toNat index)

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient == dividend

factorial : Nat -> Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

naturalDiv : Nat -> Nat -> Nat
naturalDiv numerator zero =
  numerator
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

putnam-2017-b6-solution : Nat
putnam-2017-b6-solution =
  naturalDiv (factorial 2016) (factorial 1953) -
  factorial 63 * 2016

Tuple64 : Set
Tuple64 =
  Fin 64 -> Nat

TupleEqual : Tuple64 -> Tuple64 -> Set
TupleEqual left right =
  (index : Fin 64) ->
  left index == right index

InjectiveTuple : Tuple64 -> Set
InjectiveTuple tuple =
  (left-index right-index : Fin 64) ->
  tuple left-index == tuple right-index ->
  left-index == right-index

InRange : Tuple64 -> Set
InRange tuple =
  (index : Fin 64) ->
  suc zero <=N tuple index
  and
  tuple index <=N 2017

weightedTerm : Tuple64 -> Fin 64 -> Nat
weightedTerm tuple fzero =
  tuple fzero
weightedTerm tuple (fsuc fzero) =
  tuple (fsuc fzero)
weightedTerm tuple (fsuc (fsuc index)) =
  suc (suc (toNat index)) * tuple (fsuc (fsuc index))

sumFin :
  (n : Nat) ->
  (Fin n -> Nat) ->
  Nat
sumFin zero term =
  zero
sumFin (suc n) term =
  term fzero +
  sumFin n (\ index -> term (fsuc index))

WeightedSum : Tuple64 -> Nat
WeightedSum tuple =
  sumFin 64 (weightedTerm tuple)

ValidTuple : Tuple64 -> Set
ValidTuple tuple =
  InRange tuple
  and
  InjectiveTuple tuple
  and
  (2017 divides WeightedSum tuple)

record HasExtensionalCardinality
  {A : Set}
  (_~_ : A -> A -> Set)
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
        (\ index -> item ~ enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index ~ enumerate right-index ->
      left-index == right-index

putnam-2017-b6 : Set
putnam-2017-b6 =
  HasExtensionalCardinality
    TupleEqual
    ValidTuple
    putnam-2017-b6-solution
