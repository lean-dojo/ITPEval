-- Statement-only formalization of PutnamBench corpus artifact putnam_2003_b2
-- (putnambench__agda__putnam_2003_b2): repeated averaging of the rational
-- sequence 1, 1/2, ..., 1/n yields a final value less than 2/n.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2003B2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _<=N_ _<N_ _~Q_ _<Q_
infixr 3 _and_

data Bottom : Set where

data Top : Set where
  top : Top

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

data Positive : Nat -> Set where
  positive : (n : Nat) -> Positive (suc n)

pred : Nat -> Nat
pred zero =
  zero
pred (suc n) =
  n

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
scaleInt z n =
  multiplyInt z (pos n)

IntStrictLess : Int -> Int -> Set
IntStrictLess (pos m) (pos n) =
  m <N n
IntStrictLess (pos m) (negsuc n) =
  Bottom
IntStrictLess (negsuc m) (pos n) =
  Top
IntStrictLess (negsuc m) (negsuc n) =
  n <N m

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
x ~Q y =
  scaleInt (numerator x) (denominator y) ==
  scaleInt (numerator y) (denominator x)

_<Q_ : Rational -> Rational -> Set
x <Q y =
  IntStrictLess
    (scaleInt (numerator x) (denominator y))
    (scaleInt (numerator y) (denominator x))

zeroQ : Rational
zeroQ =
  fraction (pos zero) zero

addQ : Rational -> Rational -> Rational
addQ x y =
  fraction
    (addInt
      (scaleInt (numerator x) (denominator y))
      (scaleInt (numerator y) (denominator x)))
    (pred (denominator x * denominator y))

divideByNat : Rational -> Nat -> Rational
divideByNat q zero =
  zeroQ
divideByNat q (suc n) =
  fraction
    (numerator q)
    (pred (denominator q * suc n))

naturalRatio : Nat -> Nat -> Rational
naturalRatio numerator-value zero =
  zeroQ
naturalRatio numerator-value (suc denominator-minus-one-value) =
  fraction
    (pos numerator-value)
    denominator-minus-one-value

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

InClosedNatInterval :
  Nat ->
  Nat ->
  Nat ->
  Set
InClosedNatInterval lower upper value =
  lower <=N value
  and
  value <=N upper

averageQ : Rational -> Rational -> Rational
averageQ x y =
  divideByNat (addQ x y) twoN

putnam-2003-b2 : Set
putnam-2003-b2 =
  (n : Nat) ->
  Positive n ->
  (seq : Nat -> Nat -> Rational) ->
  ((j : Nat) ->
    InClosedNatInterval oneN n j ->
    seq zero j ~Q naturalRatio oneN j) ->
  ((k : Nat) ->
    InClosedNatInterval oneN (n - oneN) k ->
    (j : Nat) ->
    InClosedNatInterval oneN (n - k) j ->
    seq k j ~Q
      averageQ
        (seq (k - oneN) j)
        (seq (k - oneN) (j + oneN))) ->
  seq (n - oneN) oneN <Q naturalRatio twoN n
