-- Statement-only formalization of PutnamBench corpus artifact putnam_2005_a1
-- (putnambench__agda__putnam_2005_a1): every positive integer is a finite sum
-- of numbers 2^r * 3^s with nonnegative exponents, with no summand dividing
-- another. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2005A1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _divides_
infixr 3 _and_

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
    first  : A
    second : B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record _divides_ (divisor dividend : Nat) : Set where
  constructor divisibility
  field
    quotient : Nat
    equation : divisor * quotient == dividend

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

naturalPower : Nat -> Nat -> Nat
naturalPower base zero =
  one
naturalPower base (suc exponent) =
  naturalPower base exponent * base

sumFin :
  {k : Nat} ->
  (Fin k -> Nat) ->
  Nat
sumFin {zero} term =
  zero
sumFin {suc k} term =
  term fzero + sumFin (\ i -> term (fsuc i))

summand :
  {k : Nat} ->
  (Fin k -> Fin two -> Nat) ->
  Fin k ->
  Nat
summand exponents i =
  naturalPower two (exponents i fzero) *
  naturalPower three (exponents i (fsuc fzero))

PairwiseNondividing :
  {k : Nat} ->
  (Fin k -> Fin two -> Nat) ->
  Set
PairwiseNondividing {k} exponents =
  (i j : Fin k) ->
  i != j ->
  Not (summand exponents i divides summand exponents j)

PositiveInteger : Int -> Set
PositiveInteger n =
  Exists Nat (\ predecessor -> n == pos (suc predecessor))

putnam-2005-a1 : Set
putnam-2005-a1 =
  (n : Int) ->
  PositiveInteger n ->
  Exists Nat
    (\ k ->
      Exists (Fin k -> Fin two -> Nat)
        (\ exponents ->
          (n == pos (sumFin (summand exponents)))
          and
          PairwiseNondividing exponents))
