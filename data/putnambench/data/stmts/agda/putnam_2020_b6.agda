-- Statement-only formalization of PutnamBench corpus artifact putnam_2020_b6
-- (putnambench__agda__putnam_2020_b6): nonnegativity of the finite real sum
-- of (-1) raised to floor(k(sqrt 2 - 1)) for 1 <= k <= n.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2020B6 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
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

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse squareRoot : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x oneR == x
    multiply-zero :
      (x : R) -> multiply x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR == zeroR
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiply x (inverse x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqual x x
    order-transitive :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual y z ->
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqual x y ->
      lessOrEqual y x ->
      x == y
    order-total :
      (x y : R) ->
      lessOrEqual x y or lessOrEqual y x
    add-order :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqual zeroR x ->
      lessOrEqual zeroR y ->
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR and zeroR != oneR

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat
        (\ n ->
          lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqual x upper) ->
            lessOrEqual supremum upper))

    square-root-nonnegative :
      (x : R) ->
      lessOrEqual zeroR (squareRoot x)
    square-root-square :
      (x : R) ->
      lessOrEqual zeroR x ->
      multiply (squareRoot x) (squareRoot x) == x
    square-root-nonpositive :
      (x : R) ->
      lessOrEqual x zeroR ->
      squareRoot x == zeroR
    square-root-unique :
      (x y : R) ->
      lessOrEqual zeroR y ->
      multiply y y == x ->
      y == squareRoot x

open CompleteOrderedRealField

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

fromInt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

successorInt : Int -> Int
successorInt (pos n) =
  pos (suc n)
successorInt (negsuc zero) =
  pos zero
successorInt (negsuc (suc n)) =
  negsuc n

record StandardFloor
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    floor : R -> Int

    floor-lower :
      (x : R) ->
      lessOrEqual reals
        (fromInt reals (floor x))
        x
    floor-upper :
      (x : R) ->
      StrictLess reals
        x
        (fromInt reals (successorInt (floor x)))
    floor-unique :
      (x : R) ->
      (z : Int) ->
      lessOrEqual reals (fromInt reals z) x ->
      StrictLess reals x (fromInt reals (successorInt z)) ->
      floor x == z

open StandardFloor

naturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc n) =
  multiply reals
    (naturalPower reals x n)
    x

integerPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Int ->
  R
integerPower reals x (pos n) =
  naturalPower reals x n
integerPower reals x (negsuc n) =
  inverse reals
    (naturalPower reals x (suc n))

sumThrough :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumThrough reals zero term =
  zeroR reals
sumThrough reals (suc n) term =
  add reals
    (sumThrough reals n term)
    (term (suc n))

Positive : Nat -> Set
Positive n =
  Exists Nat
    (\ predecessor ->
      n == suc predecessor)

module Putnam2020B6Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (flooring : StandardFloor reals) where

  twoN : Nat
  twoN =
    suc (suc zero)

  squareRootTwoMinusOne : R
  squareRootTwoMinusOne =
    subtract reals
      (squareRoot reals (fromNat reals twoN))
      (oneR reals)

  exponent : Nat -> Int
  exponent k =
    floor flooring
      (multiply reals
        (fromNat reals k)
        squareRootTwoMinusOne)

  term : Nat -> R
  term k =
    integerPower reals
      (negate reals (oneR reals))
      (exponent k)

  partialSum : Nat -> R
  partialSum n =
    sumThrough reals n term

  proposition : Set
  proposition =
    (n : Nat) ->
    Positive n ->
    lessOrEqual reals
      (zeroR reals)
      (partialSum n)

putnam-2020-b6 : Set1
putnam-2020-b6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (flooring : StandardFloor reals) ->
  Putnam2020B6Statement.proposition reals flooring
