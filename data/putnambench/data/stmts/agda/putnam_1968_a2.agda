-- Statement-only formalization of PutnamBench corpus artifact putnam_1968_a2:
-- rational coefficients make two integer affine expressions nonzero and
-- arbitrarily small when the associated determinant is nonzero. This file
-- contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

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

absoluteInt : Int -> Int
absoluteInt (pos n) = pos n
absoluteInt (negsuc n) = pos (suc n)

scaleInt : Int -> Nat -> Int
scaleInt z n = multiplyInt z (pos n)

record Rational : Set where
  constructor fraction
  field
    numerator             : Int
    denominator-minus-one : Nat

open Rational

denominator : Rational -> Nat
denominator q = suc (denominator-minus-one q)

zeroQ : Rational
zeroQ = fraction (pos zero) zero

rationalFromInt : Int -> Rational
rationalFromInt z = fraction z zero

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

subtractQ : Rational -> Rational -> Rational
subtractQ x y = addQ x (negateQ y)

multiplyQ : Rational -> Rational -> Rational
multiplyQ x y =
  fraction
    (multiplyInt (numerator x) (numerator y))
    (pred (denominator x * denominator y))

absoluteQ : Rational -> Rational
absoluteQ q =
  fraction
    (absoluteInt (numerator q))
    (denominator-minus-one q)

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR inverseR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> addR x y == addR y x
    add-associative :
      (x y z : R) -> addR (addR x y) z == addR x (addR y z)
    add-zero :
      (x : R) -> addR x zeroR == x
    add-inverse :
      (x : R) -> addR x (negateR x) == zeroR

    multiply-commutative :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiply-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)
    multiply-one :
      (x : R) -> multiplyR x oneR == x
    multiply-zero :
      (x : R) -> multiplyR x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    inverse-zero :
      inverseR zeroR == zeroR
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiplyR x (inverseR x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqualR x x
    order-transitive :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y
    order-total :
      (x y : R) ->
      lessOrEqualR x y or lessOrEqualR y x
    add-order :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-one :
      lessOrEqualR zeroR oneR and zeroR != oneR

    fromNat-zero :
      fromNatR zero == zeroR
    fromNat-successor :
      (n : Nat) -> fromNatR (suc n) == addR (fromNatR n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNatR (m + n) == addR (fromNatR m) (fromNatR n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNatR (m * n) == multiplyR (fromNatR m) (fromNatR n)
    fromNat-injective :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) -> P x -> lessOrEqualR x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqualR x upper) ->
            lessOrEqualR supremum upper))

open CompleteOrderedField

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  addR reals x (negateR reals y)

divideR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divideR reals x y =
  multiplyR reals x (inverseR reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqualR reals x y and x != y

fromIntR :
  {R : Set} ->
  CompleteOrderedField R ->
  Int ->
  R
fromIntR reals (pos n) =
  fromNatR reals n
fromIntR reals (negsuc n) =
  negateR reals (fromNatR reals (suc n))

fromRationalR :
  {R : Set} ->
  CompleteOrderedField R ->
  Rational ->
  R
fromRationalR reals q =
  divideR reals
    (fromIntR reals (numerator q))
    (fromNatR reals (denominator q))

affineError :
  Rational ->
  Rational ->
  Int ->
  Int ->
  Int ->
  Rational
affineError r s x y target =
  subtractQ
    (addQ
      (multiplyQ r (rationalFromInt x))
      (multiplyQ s (rationalFromInt y)))
    (rationalFromInt target)

AbsoluteErrorBetweenZeroAnd :
  {R : Set} ->
  CompleteOrderedField R ->
  Rational ->
  Rational ->
  Int ->
  Int ->
  Int ->
  R ->
  Set
AbsoluteErrorBetweenZeroAnd reals r s x y target epsilon =
  let
    error =
      fromRationalR reals
        (absoluteQ (affineError r s x y target))
  in
  StrictLess reals (zeroR reals) error
  and
  StrictLess reals error epsilon

module Putnam1968A2Statement
  {R : Set}
  (reals : CompleteOrderedField R) where

  proposition : Set
  proposition =
    (a b c d e f : Int) ->
    (epsilon : R) ->
    multiplyInt a d != multiplyInt b c ->
    StrictLess reals (zeroR reals) epsilon ->
    Exists Rational
      (\ r ->
        Exists Rational
          (\ s ->
            AbsoluteErrorBetweenZeroAnd
              reals r s a b e epsilon
            and
            AbsoluteErrorBetweenZeroAnd
              reals r s c d f epsilon))

putnam-1968-a2 : Set1
putnam-1968-a2 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  Putnam1968A2Statement.proposition reals
