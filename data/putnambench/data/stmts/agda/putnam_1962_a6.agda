-- Statement-only formalization of PutnamBench corpus artifact putnam_1962_a6:
-- a rational subset closed under addition and multiplication, for which exactly
-- one of r being a member, -r being a member, and r being zero holds, is the
-- set of positive rationals. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _~Q_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

record And (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Or (A B : Set) : Set where
  left  : A -> Or A B
  right : B -> Or A B

record Iff (A B : Set) : Set where
  constructor iff
  field
    forward  : A -> B
    backward : B -> A

pred : Nat -> Nat
pred zero = zero
pred (suc n) = n

negative : Nat -> Int
negative zero = pos zero
negative (suc n) = negsuc n

negateInt : Int -> Int
negateInt (pos n) = negative n
negateInt (negsuc n) = pos (suc n)

difference : Nat -> Nat -> Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = difference m (suc n)
addInt (negsuc m) (pos n) = difference n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) = negative (m * suc n)
multiplyInt (negsuc m) (pos n) = negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

scaleInt : Int -> Nat -> Int
scaleInt z n = multiplyInt z (pos n)

record Rational : Set where
  constructor fraction
  field
    numerator             : Int
    denominator-minus-one : Nat

open Rational public

denominator : Rational -> Nat
denominator q = suc (denominator-minus-one q)

_~Q_ : Rational -> Rational -> Set
x ~Q y =
  scaleInt (numerator x) (denominator y) ==
  scaleInt (numerator y) (denominator x)

zeroQ : Rational
zeroQ = fraction (pos zero) zero

negateQ : Rational -> Rational
negateQ q =
  fraction
    (negateInt (numerator q))
    (denominator-minus-one q)

addQ : Rational -> Rational -> Rational
addQ x y =
  fraction
    (addInt
      (scaleInt (numerator x) (denominator y))
      (scaleInt (numerator y) (denominator x)))
    (pred (denominator x * denominator y))

multiplyQ : Rational -> Rational -> Rational
multiplyQ x y =
  fraction
    (multiplyInt (numerator x) (numerator y))
    (pred (denominator x * denominator y))

data PositiveInt : Int -> Set where
  positive : {n : Nat} -> PositiveInt (pos (suc n))

PositiveRational : Rational -> Set
PositiveRational q = PositiveInt (numerator q)

record RationalSubset : Set1 where
  field
    contains : Rational -> Set
    respects-rational-equality :
      (x y : Rational) ->
      x ~Q y ->
      Iff (contains x) (contains y)

open RationalSubset public

AdditionClosed : RationalSubset -> Set
AdditionClosed S =
  (a b : Rational) ->
  contains S a ->
  contains S b ->
  contains S (addQ a b)

MultiplicationClosed : RationalSubset -> Set
MultiplicationClosed S =
  (a b : Rational) ->
  contains S a ->
  contains S b ->
  contains S (multiplyQ a b)

ExactlyOneCondition : RationalSubset -> Set
ExactlyOneCondition S =
  (r : Rational) ->
  And
    (Or
      (contains S r)
      (Or (contains S (negateQ r)) (r ~Q zeroQ)))
    (And
      (Not (And (contains S r) (contains S (negateQ r))))
      (And
        (Not (And (contains S r) (r ~Q zeroQ)))
        (Not (And (contains S (negateQ r)) (r ~Q zeroQ)))))

SameSubsetAsPositiveRationals : RationalSubset -> Set
SameSubsetAsPositiveRationals S =
  (r : Rational) ->
  Iff (contains S r) (PositiveRational r)

putnam-1962-a6 : Set1
putnam-1962-a6 =
  (S : RationalSubset) ->
  AdditionClosed S ->
  MultiplicationClosed S ->
  ExactlyOneCondition S ->
  SameSubsetAsPositiveRationals S
