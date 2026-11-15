-- Statement-only formalization of PutnamBench corpus artifact putnam_2023_b4
-- (putnambench__agda__putnam_2023_b4): the least nonnegative time for the
-- specified piecewise-accelerating real function to reach 2023 is 29.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

finToNat : {n : Nat} -> Fin n -> Nat
finToNat fzero =
  zero
finToNat (fsuc index) =
  suc (finToNat index)

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
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

open CompleteOrderedRealField

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

CloseTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals
    (subtract reals center radius)
    x
  and
  StrictLess reals
    x
    (add reals center radius)

ContinuousWithinAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> Set) ->
  (R -> R) ->
  R ->
  Set
ContinuousWithinAt {R} reals domain function point =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        domain x ->
        CloseTo reals point delta x ->
        CloseTo reals
          (function point)
          epsilon
          (function x)))

ContinuousOn :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> Set) ->
  (R -> R) ->
  Set
ContinuousOn {R} reals domain function =
  (point : R) ->
  domain point ->
  ContinuousWithinAt reals domain function point

DerivativeWithinAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> Set) ->
  (R -> R) ->
  R ->
  R ->
  Set
DerivativeWithinAt {R} reals domain function point derivativeValue =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        domain x ->
        CloseTo reals point delta x ->
        x != point ->
        CloseTo reals derivativeValue epsilon
          (divide reals
            (subtract reals (function x) (function point))
            (subtract reals x point))))

RightLimitAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  Set
RightLimitAt {R} reals function point limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        StrictLess reals point x ->
        StrictLess reals x (add reals point delta) ->
        CloseTo reals limit epsilon (function x)))

module Putnam2023B4Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  PuncturedHalfLine :
    Nat ->
    (Nat -> R) ->
    R ->
    Set
  PuncturedHalfLine n times t =
    StrictLess reals (times zero) t
    and
    ((index : Fin n) ->
      t != times (suc (finToNat index)))

  ClosedHalfLine :
    R ->
    R ->
    Set
  ClosedHalfLine lower x =
    lessOrEqual reals lower x

  record TwiceDifferentiableData
    (n : Nat)
    (times : Nat -> R)
    (function : R -> R) :
    Set where

    field
      firstDerivative secondDerivative : R -> R

      first-derivative-correct :
        (x : R) ->
        PuncturedHalfLine n times x ->
        DerivativeWithinAt reals
          (PuncturedHalfLine n times)
          function
          x
          (firstDerivative x)

      first-derivative-continuous :
        ContinuousOn reals
          (PuncturedHalfLine n times)
          firstDerivative

      second-derivative-correct :
        (x : R) ->
        PuncturedHalfLine n times x ->
        DerivativeWithinAt reals
          (PuncturedHalfLine n times)
          firstDerivative
          x
          (secondDerivative x)

  open TwiceDifferentiableData

  SpacedTimes :
    Nat ->
    (Nat -> R) ->
    Set
  SpacedTimes n times =
    (index : Fin n) ->
    lessOrEqual reals
      (add reals
        (times (finToNat index))
        (oneR reals))
      (times (suc (finToNat index)))

  FunctionConditions :
    (n : Nat) ->
    (times : Nat -> R) ->
    (function : R -> R) ->
    TwiceDifferentiableData n times function ->
    Set
  FunctionConditions n times function derivatives =
    ContinuousOn reals
      (ClosedHalfLine (times zero))
      function
    and
    function (times zero) ==
      divide reals
        (oneR reals)
        (fromNat reals 2)
    and
    ((index : Fin (suc n)) ->
      RightLimitAt reals
        (firstDerivative derivatives)
        (times (finToNat index))
        (zeroR reals))
    and
    ((index : Fin n) ->
      (t : R) ->
      StrictLess reals
        (times (finToNat index))
        t ->
      StrictLess reals
        t
        (times (suc (finToNat index))) ->
      secondDerivative derivatives t ==
        fromNat reals (suc (finToNat index)))
    and
    ((t : R) ->
      StrictLess reals (times n) t ->
      secondDerivative derivatives t ==
        fromNat reals (suc n))

  AdmissibleTime : R -> Set
  AdmissibleTime T =
    lessOrEqual reals (zeroR reals) T
    and
    Exists Nat
      (\ n ->
        Exists (Nat -> R)
          (\ times ->
            Exists (R -> R)
              (\ function ->
                SpacedTimes n times
                and
                Exists
                  (TwiceDifferentiableData n times function)
                  (\ derivatives ->
                    FunctionConditions
                      n
                      times
                      function
                      derivatives
                    and
                    function
                      (add reals (times zero) T)
                    ==
                    fromNat reals 2023))))

  IsLeastAdmissibleTime : R -> Set
  IsLeastAdmissibleTime leastTime =
    AdmissibleTime leastTime
    and
    ((T : R) ->
      AdmissibleTime T ->
      lessOrEqual reals leastTime T)

  proposition : Set
  proposition =
    IsLeastAdmissibleTime (fromNat reals 29)

putnam-2023-b4 : Set1
putnam-2023-b4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2023B4Statement.proposition reals
