-- Statement-only formalization of PutnamBench corpus artifact putnam_2011_b2
-- (putnambench__agda__putnam_2011_b2): the primes occurring in at least seven
-- prime triples whose quadratic has a rational root are exactly 2 and 5.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2011B2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_ _~Q_
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
    factor : Nat
    equation : divisor * factor == number

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

fiveN : Nat
fiveN =
  suc (suc (suc twoN))

sevenN : Nat
sevenN =
  suc (suc fiveN)

Prime : Nat -> Set
Prime number =
  twoN <=N number
  and
  ((divisor : Nat) ->
    Divides divisor number ->
    divisor == oneN or divisor == number)

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

scaleInt : Int -> Nat -> Int
scaleInt integer natural =
  multiplyInt integer (pos natural)

predecessor : Nat -> Nat
predecessor zero =
  zero
predecessor (suc n) =
  n

record Rational : Set where
  constructor fraction
  field
    numerator             : Int
    denominator-minus-one : Nat

open Rational

denominator : Rational -> Nat
denominator rational =
  suc (denominator-minus-one rational)

_~Q_ : Rational -> Rational -> Set
left-rational ~Q right-rational =
  scaleInt
    (numerator left-rational)
    (denominator right-rational)
  ==
  scaleInt
    (numerator right-rational)
    (denominator left-rational)

zeroQ : Rational
zeroQ =
  fraction (pos zero) zero

naturalQ : Nat -> Rational
naturalQ natural =
  fraction (pos natural) zero

addQ : Rational -> Rational -> Rational
addQ left-rational right-rational =
  fraction
    (addInt
      (scaleInt
        (numerator left-rational)
        (denominator right-rational))
      (scaleInt
        (numerator right-rational)
        (denominator left-rational)))
    (predecessor
      (denominator left-rational * denominator right-rational))

multiplyQ : Rational -> Rational -> Rational
multiplyQ left-rational right-rational =
  fraction
    (multiplyInt
      (numerator left-rational)
      (numerator right-rational))
    (predecessor
      (denominator left-rational * denominator right-rational))

record Triple : Set where
  constructor triple
  field
    first-coordinate  : Nat
    second-coordinate : Nat
    third-coordinate  : Nat

open Triple

HasRationalRoot : Triple -> Set
HasRationalRoot coefficients =
  Exists Rational
    (\ x ->
      addQ
        (addQ
          (multiplyQ
            (naturalQ (first-coordinate coefficients))
            (multiplyQ x x))
          (multiplyQ
            (naturalQ (second-coordinate coefficients))
            x))
        (naturalQ (third-coordinate coefficients))
      ~Q zeroQ)

QualifiedTriple : Triple -> Set
QualifiedTriple coefficients =
  Prime (first-coordinate coefficients)
  and
  Prime (second-coordinate coefficients)
  and
  Prime (third-coordinate coefficients)
  and
  HasRationalRoot coefficients

Contains : Nat -> Triple -> Set
Contains number coefficients =
  first-coordinate coefficients == number
  or
  second-coordinate coefficients == number
  or
  third-coordinate coefficients == number

SameSet :
  (Triple -> Set) ->
  (Triple -> Set) ->
  Set
SameSet left-set right-set =
  (coefficients : Triple) ->
  Iff
    (left-set coefficients)
    (right-set coefficients)

AppearsAtLeastSevenTimes :
  (Triple -> Set) ->
  Nat ->
  Set
AppearsAtLeastSevenTimes S number =
  AtLeastCardinality
    (\ coefficients ->
      S coefficients
      and
      Contains number coefficients)
    sevenN

putnam-2011-b2-solution : Nat -> Set
putnam-2011-b2-solution number =
  number == twoN or number == fiveN

putnam-2011-b2 : Set1
putnam-2011-b2 =
  (S : Triple -> Set) ->
  (t : Nat) ->
  SameSet S QualifiedTriple ->
  Iff
    (Prime t and AppearsAtLeastSevenTimes S t)
    (putnam-2011-b2-solution t)
