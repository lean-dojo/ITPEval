-- Statement-only formalization of PutnamBench corpus artifact putnam_2021_a6
-- (putnambench__agda__putnam_2021_a6): a 0/1-coefficient integer polynomial
-- that factors into two positive-degree integer polynomials has composite
-- value at 2. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2021A6 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
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

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

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
negateInt (pos zero) =
  pos zero
negateInt (pos (suc n)) =
  negsuc n
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

zeroZ : Int
zeroZ =
  pos zero

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

minusOneZ : Int
minusOneZ =
  negsuc zero

Polynomial : Set
Polynomial =
  List Int

coefficient : Polynomial -> Nat -> Int
coefficient [] n =
  zeroZ
coefficient (c ∷ coefficients) zero =
  c
coefficient (c ∷ coefficients) (suc n) =
  coefficient coefficients n

PolynomialEqual : Polynomial -> Polynomial -> Set
PolynomialEqual p q =
  (n : Nat) ->
  coefficient p n == coefficient q n

addPolynomials : Polynomial -> Polynomial -> Polynomial
addPolynomials [] q =
  q
addPolynomials p [] =
  p
addPolynomials (a ∷ p) (b ∷ q) =
  addInt a b ∷ addPolynomials p q

scalePolynomial : Int -> Polynomial -> Polynomial
scalePolynomial scalar [] =
  []
scalePolynomial scalar (c ∷ coefficients) =
  multiplyInt scalar c ∷ scalePolynomial scalar coefficients

multiplyPolynomials : Polynomial -> Polynomial -> Polynomial
multiplyPolynomials [] q =
  []
multiplyPolynomials (c ∷ coefficients) q =
  addPolynomials
    (scalePolynomial c q)
    (zeroZ ∷ multiplyPolynomials coefficients q)

evaluate : Polynomial -> Int -> Int
evaluate [] x =
  zeroZ
evaluate (c ∷ coefficients) x =
  addInt c
    (multiplyInt x (evaluate coefficients x))

AllCoefficientsZeroOrOne : Polynomial -> Set
AllCoefficientsZeroOrOne polynomial =
  (n : Nat) ->
  coefficient polynomial n == zeroZ
  or
  coefficient polynomial n == oneZ

PositiveDegree : Polynomial -> Set
PositiveDegree polynomial =
  Exists Nat
    (\ degree ->
      Positive degree
      and
      coefficient polynomial degree != zeroZ)

FactorableIntoPositiveDegrees : Polynomial -> Set
FactorableIntoPositiveDegrees polynomial =
  Exists Polynomial
    (\ leftFactor ->
      Exists Polynomial
        (\ rightFactor ->
          PositiveDegree leftFactor
          and
          PositiveDegree rightFactor
          and
          PolynomialEqual polynomial
            (multiplyPolynomials leftFactor rightFactor)))

DividesInt : Int -> Int -> Set
DividesInt divisor dividend =
  Exists Int
    (\ quotient ->
      multiplyInt divisor quotient == dividend)

UnitInt : Int -> Set
UnitInt integer =
  integer == oneZ
  or
  integer == minusOneZ

AssociatesInt : Int -> Int -> Set
AssociatesInt leftInteger rightInteger =
  leftInteger == rightInteger
  or
  leftInteger == negateInt rightInteger

PrimeInt : Int -> Set
PrimeInt integer =
  integer != zeroZ
  and
  Not (UnitInt integer)
  and
  ((divisor : Int) ->
    DividesInt divisor integer ->
    UnitInt divisor or AssociatesInt divisor integer)

CompositeConclusion : Int -> Set
CompositeConclusion integer =
  integer != zeroZ
  and
  integer != oneZ
  and
  Not (PrimeInt integer)

putnam-2021-a6 : Set
putnam-2021-a6 =
  (polynomial : Polynomial) ->
  AllCoefficientsZeroOrOne polynomial ->
  FactorableIntoPositiveDegrees polynomial ->
  CompositeConclusion (evaluate polynomial twoZ)
