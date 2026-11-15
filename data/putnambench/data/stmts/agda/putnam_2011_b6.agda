-- Statement-only formalization of PutnamBench corpus artifact putnam_2011_b6
-- (putnambench__agda__putnam_2011_b6): for an odd prime p, the factorial
-- polynomial sum is nonzero modulo p at at least (p + 1) / 2 residues below p.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2011B6 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<N_
infixr 3 _and_
infixr 2 _or_

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

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record AtLeastCardinality
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

    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

record Divides (divisor number : Nat) : Set where
  constructor divides
  field
    quotient : Nat
    equation : divisor * quotient == number

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

Odd : Nat -> Set
Odd number =
  Exists Nat
    (\ half ->
      number == twoN * half + oneN)

Prime : Nat -> Set
Prime number =
  twoN <=N number
  and
  ((divisor : Nat) ->
    Divides divisor number ->
    divisor == oneN or divisor == number)

naturalPower : Nat -> Nat -> Nat
naturalPower base zero =
  oneN
naturalPower base (suc exponent) =
  naturalPower base exponent * base

factorial : Nat -> Nat
factorial zero =
  oneN
factorial (suc n) =
  suc n * factorial n

sumFirst : Nat -> (Nat -> Nat) -> Nat
sumFirst zero term =
  zero
sumFirst (suc length) term =
  sumFirst length term + term length

factorialPolynomial : Nat -> Nat -> Nat
factorialPolynomial p n =
  sumFirst p
    (\ k ->
      factorial k * naturalPower n k)

GoodResidue : Nat -> Nat -> Set
GoodResidue p n =
  n <N p
  and
  Not (Divides p (factorialPolynomial p n))

halfFloor : Nat -> Nat
halfFloor zero =
  zero
halfFloor (suc zero) =
  zero
halfFloor (suc (suc n)) =
  suc (halfFloor n)

putnam-2011-b6 : Set
putnam-2011-b6 =
  (p : Nat) ->
  Odd p ->
  Prime p ->
  AtLeastCardinality
    (GoodResidue p)
    (halfFloor (p + oneN))
