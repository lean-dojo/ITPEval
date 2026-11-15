-- Statement-only formalization of PutnamBench corpus artifact putnam_2004_b1
-- (putnambench__agda__putnam_2004_b1): integer-coefficient polynomials at
-- rational roots have integer leading partial sums. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _<=N_ _<N_ _~Q_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

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

predNat : Nat -> Nat
predNat zero =
  zero
predNat (suc n) =
  n

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

intDifference : Nat -> Nat -> Int
intDifference zero zero =
  pos zero
intDifference (suc m) zero =
  pos (suc m)
intDifference zero (suc n) =
  negsuc n
intDifference (suc m) (suc n) =
  intDifference m n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  intDifference m (suc n)
addInt (negsuc m) (pos n) =
  intDifference n (suc m)
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
scaleInt z n =
  multiplyInt z (pos n)

record Rational : Set where
  constructor fraction
  field
    numerator             : Int
    denominator-minus-one : Nat

open Rational

denominator : Rational -> Nat
denominator q =
  suc (denominator-minus-one q)

_~Q_ : Rational -> Rational -> Set
p ~Q q =
  scaleInt (numerator p) (denominator q) ==
  scaleInt (numerator q) (denominator p)

zeroQ : Rational
zeroQ =
  fraction (pos zero) zero

oneQ : Rational
oneQ =
  fraction (pos (suc zero)) zero

integerQ : Int -> Rational
integerQ z =
  fraction z zero

addQ : Rational -> Rational -> Rational
addQ p q =
  fraction
    (addInt
      (scaleInt (numerator p) (denominator q))
      (scaleInt (numerator q) (denominator p)))
    (predNat (denominator p * denominator q))

multiplyQ : Rational -> Rational -> Rational
multiplyQ p q =
  fraction
    (multiplyInt (numerator p) (numerator q))
    (predNat (denominator p * denominator q))

powerQ : Rational -> Nat -> Rational
powerQ q zero =
  oneQ
powerQ q (suc n) =
  multiplyQ q (powerQ q n)

sumFirst : Nat -> (Nat -> Rational) -> Rational
sumFirst zero term =
  zeroQ
sumFirst (suc n) term =
  addQ
    (sumFirst n term)
    (term n)

record DegreeExactly (coefficients : Nat -> Int) (n : Nat) : Set where
  constructor exactDegree
  field
    leading-nonzero :
      Not (coefficients n == pos zero)
    coefficients-above-zero :
      (k : Nat) ->
      n <N k ->
      coefficients k == pos zero

polynomialValue :
  (Nat -> Int) ->
  Nat ->
  Rational ->
  Rational
polynomialValue coefficients n r =
  sumFirst (suc n)
    (\ j ->
      multiplyQ
        (integerQ (coefficients j))
        (powerQ r j))

leadingPartialSum :
  (Nat -> Int) ->
  Nat ->
  Rational ->
  Nat ->
  Rational
leadingPartialSum coefficients n r i =
  sumFirst (suc i)
    (\ j ->
      multiplyQ
        (integerQ (coefficients (n - j)))
        (powerQ r (suc i - j)))

IsIntegerQ : Rational -> Set
IsIntegerQ q =
  Exists Int
    (\ z -> integerQ z ~Q q)

putnam-2004-b1 : Set
putnam-2004-b1 =
  (n : Nat) ->
  (coefficients : Nat -> Int) ->
  (r : Rational) ->
  DegreeExactly coefficients n ->
  polynomialValue coefficients n r ~Q zeroQ ->
  (i : Nat) ->
  i <N n ->
  IsIntegerQ (leadingPartialSum coefficients n r i)
