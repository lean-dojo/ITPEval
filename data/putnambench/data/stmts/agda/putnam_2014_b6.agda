-- Statement-only formalization of PutnamBench corpus artifact putnam_2014_b6
-- (putnambench__agda__putnam_2014_b6): a Lipschitz real function with
-- integer-affine values at rational points is piecewise affine on finitely
-- many intervals covering [0,1]. This file contains no proof.

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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse absoluteValue : R -> R
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

    absolute-nonnegative :
      (x : R) -> lessOrEqual zeroR (absoluteValue x)
    absolute-of-nonnegative :
      (x : R) ->
      lessOrEqual zeroR x ->
      absoluteValue x == x
    absolute-of-nonpositive :
      (x : R) ->
      lessOrEqual x zeroR ->
      absoluteValue x == negate x

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

Between :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
Between reals lower upper x =
  lessOrEqual reals lower x
  and
  lessOrEqual reals x upper

fromInt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

record Rational : Set where
  constructor fraction
  field
    numerator             : Int
    denominator-minus-one : Nat

open Rational

denominator : Rational -> Nat
denominator q =
  suc (denominator-minus-one q)

rationalValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Rational ->
  R
rationalValue reals q =
  multiply reals
    (fromInt reals (numerator q))
    (inverse reals (fromNat reals (denominator q)))

record ClosedInterval
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set where

  field
    lower upper : R
    ordered :
      lessOrEqual reals lower upper

open ClosedInterval

InClosedInterval :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  ClosedInterval reals ->
  R ->
  Set
InClosedInterval reals interval x =
  Between reals
    (lower interval)
    (upper interval)
    x

module Putnam2014B6Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  UnitInterval : R -> Set
  UnitInterval x =
    Between reals
      (zeroR reals)
      (oneR reals)
      x

  LipschitzOnUnitInterval : (R -> R) -> Set
  LipschitzOnUnitInterval f =
    Exists R
      (\ K ->
        StrictLess reals (zeroR reals) K
        and
        ((x y : R) ->
          UnitInterval x ->
          UnitInterval y ->
          lessOrEqual reals
            (absoluteValue reals
              (subtract reals (f x) (f y)))
            (multiply reals K
              (absoluteValue reals
                (subtract reals x y)))))

  HasIntegerAffineValuesAtRationals : (R -> R) -> Set
  HasIntegerAffineValuesAtRationals f =
    (q : Rational) ->
    UnitInterval (rationalValue reals q) ->
    Exists Int
      (\ a ->
        Exists Int
          (\ b ->
            f (rationalValue reals q)
            ==
            add reals
              (fromInt reals a)
              (multiply reals
                (fromInt reals b)
                (rationalValue reals q))))

  AffineOn :
    (R -> R) ->
    ClosedInterval reals ->
    Set
  AffineOn f interval =
    Exists R
      (\ m ->
        Exists R
          (\ c ->
            (x : R) ->
            InClosedInterval reals interval x ->
            f x ==
            add reals c (multiply reals m x)))

  FiniteAffineIntervalCover : (R -> R) -> Set
  FiniteAffineIntervalCover f =
    Exists Nat
      (\ count ->
        Exists (Fin count -> ClosedInterval reals)
          (\ intervals ->
            ((index : Fin count) ->
              AffineOn f (intervals index))
            and
            ((x : R) ->
              Iff
                (UnitInterval x)
                (Exists (Fin count)
                  (\ index ->
                    InClosedInterval reals
                      (intervals index)
                      x)))))

  proposition : Set
  proposition =
    (f : R -> R) ->
    LipschitzOnUnitInterval f ->
    HasIntegerAffineValuesAtRationals f ->
    FiniteAffineIntervalCover f

putnam-2014-b6 : Set1
putnam-2014-b6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2014B6Statement.proposition reals
