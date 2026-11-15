-- Statement-only formalization of PutnamBench corpus artifact putnam_2007_b3
-- (putnambench__agda__putnam_2007_b3): the real recurrence using
-- floor(x_n * sqrt(5)) has the specified closed form at n = 2007.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

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

intSuccessor : Int -> Int
intSuccessor (pos n) =
  pos (suc n)
intSuccessor (negsuc zero) =
  pos zero
intSuccessor (negsuc (suc n)) =
  negsuc n

embedInt :
  {R : Set} ->
  (Nat -> R) ->
  (R -> R) ->
  Int ->
  R
embedInt fromNatural negateR (pos n) =
  fromNatural n
embedInt fromNatural negateR (negsuc n) =
  negateR (fromNatural (suc n))

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse squareRoot : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R
    floor : R -> Int

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
      Exists Nat (\ n -> lessOrEqual x (fromNat n))
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

    floor-lower :
      (x : R) ->
      lessOrEqual
        (embedInt fromNat negate (floor x))
        x
    floor-upper :
      (x : R) ->
      lessOrEqual
        x
        (embedInt fromNat negate (intSuccessor (floor x)))
      and
      x != embedInt fromNat negate (intSuccessor (floor x))

open CompleteOrderedRealField

fromInt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
fromInt reals =
  embedInt (fromNat reals) (negate reals)

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

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
  inverse reals (naturalPower reals x (suc n))

module Putnam2007B3Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  two three five : R
  two =
    fromNat reals 2
  three =
    fromNat reals 3
  five =
    fromNat reals 5

  sqrtFive : R
  sqrtFive =
    squareRoot reals five

  goldenRatio : R
  goldenRatio =
    divide reals
      (add reals (oneR reals) sqrtFive)
      two

  solution : R
  solution =
    multiply reals
      (divide reals
        (naturalPower reals two 2006)
        sqrtFive)
      (add reals
        (naturalPower reals goldenRatio 4017)
        (integerPower reals goldenRatio (negsuc 4016)))

  proposition : Set
  proposition =
    (x : Nat -> R) ->
    x zero == oneR reals ->
    ((n : Nat) ->
      x (suc n) ==
      add reals
        (multiply reals three (x n))
        (fromInt reals
          (floor reals
            (multiply reals (x n) sqrtFive)))) ->
    x 2007 == solution

putnam-2007-b3 : Set1
putnam-2007-b3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2007B3Statement.proposition reals
