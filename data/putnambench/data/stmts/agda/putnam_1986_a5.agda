-- Statement-only formalization of PutnamBench corpus artifact putnam_1986_a5:
-- a real vector field with continuous second partial derivatives and constant
-- skew first-partial differences admits a potential correction whose components
-- are linear. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1986A5 where

open import Agda.Builtin.Bool using (Bool; false; true)
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

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

finEqual :
  {n : Nat} ->
  Fin n ->
  Fin n ->
  Bool
finEqual fzero fzero =
  true
finEqual fzero (fsuc j) =
  false
finEqual (fsuc i) fzero =
  false
finEqual (fsuc i) (fsuc j) =
  finEqual i j

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

differenceQuotient :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  R
differenceQuotient reals function point x =
  divide reals
    (subtract reals (function x) (function point))
    (subtract reals x point)

DerivativeAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  Set
DerivativeAt {R} reals function point derivativeValue =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        CloseTo reals point delta x ->
        x != point ->
        CloseTo reals derivativeValue epsilon
          (differenceQuotient reals function point x)))

HasDerivativeAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  Set
HasDerivativeAt {R} reals function point =
  Exists R
    (\ derivativeValue ->
      DerivativeAt reals function point derivativeValue)

record StandardRealCalculus
  {R : Set}
  (reals : CompleteOrderedRealField R) : Set1 where

  field
    derivative : (R -> R) -> R -> R

    derivative-when-differentiable :
      (function : R -> R) ->
      (point : R) ->
      HasDerivativeAt reals function point ->
      DerivativeAt reals
        function
        point
        (derivative function point)

    derivative-when-not-differentiable :
      (function : R -> R) ->
      (point : R) ->
      Not (HasDerivativeAt reals function point) ->
      derivative function point == zeroR reals

open StandardRealCalculus

Vector :
  Nat ->
  Set ->
  Set
Vector n R =
  Fin n -> R

replaceCoordinate :
  {n : Nat} {R : Set} ->
  Vector n R ->
  Fin n ->
  R ->
  Vector n R
replaceCoordinate x i value j with finEqual i j
... | true =
  value
... | false =
  x j

zeroVector :
  {n : Nat} {R : Set} ->
  CompleteOrderedRealField R ->
  Vector n R
zeroVector reals i =
  zeroR reals

addVector :
  {n : Nat} {R : Set} ->
  CompleteOrderedRealField R ->
  Vector n R ->
  Vector n R ->
  Vector n R
addVector reals x y i =
  add reals (x i) (y i)

scaleVector :
  {n : Nat} {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Vector n R ->
  Vector n R
scaleVector reals scalar x i =
  multiply reals scalar (x i)

VectorClose :
  {n : Nat} {R : Set} ->
  CompleteOrderedRealField R ->
  Vector n R ->
  R ->
  Vector n R ->
  Set
VectorClose {n} reals center radius x =
  (i : Fin n) ->
  CloseTo reals (center i) radius (x i)

ContinuousVectorFunction :
  {n : Nat} {R : Set} ->
  CompleteOrderedRealField R ->
  (Vector n R -> R) ->
  Set
ContinuousVectorFunction {n} {R} reals function =
  (point : Vector n R) ->
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : Vector n R) ->
        VectorClose reals point delta x ->
        CloseTo reals
          (function point)
          epsilon
          (function x)))

partialDerivative :
  {n : Nat} {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealCalculus reals ->
  (Vector n R -> R) ->
  Fin n ->
  Vector n R ->
  R
partialDerivative reals calculus function i x =
  derivative calculus
    (\ coordinate ->
      function (replaceCoordinate x i coordinate))
    (x i)

HasPartialDerivativeAt :
  {n : Nat} {R : Set} ->
  CompleteOrderedRealField R ->
  (Vector n R -> R) ->
  Fin n ->
  Vector n R ->
  Set
HasPartialDerivativeAt reals function i x =
  HasDerivativeAt reals
    (\ coordinate ->
      function (replaceCoordinate x i coordinate))
    (x i)

FirstPartialsExist :
  {n : Nat} {R : Set} ->
  CompleteOrderedRealField R ->
  (Vector n R -> R) ->
  Set
FirstPartialsExist {n} {R} reals function =
  (i : Fin n) ->
  (x : Vector n R) ->
  HasPartialDerivativeAt reals function i x

FirstPartialsContinuous :
  {n : Nat} {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealCalculus reals ->
  (Vector n R -> R) ->
  Set
FirstPartialsContinuous {n} reals calculus function =
  (i : Fin n) ->
  ContinuousVectorFunction reals
    (partialDerivative reals calculus function i)

SecondPartialsExist :
  {n : Nat} {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealCalculus reals ->
  (Vector n R -> R) ->
  Set
SecondPartialsExist {n} {R} reals calculus function =
  (i j : Fin n) ->
  (x : Vector n R) ->
  HasPartialDerivativeAt reals
    (partialDerivative reals calculus function i)
    j
    x

SecondPartialsContinuous :
  {n : Nat} {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealCalculus reals ->
  (Vector n R -> R) ->
  Set
SecondPartialsContinuous {n} reals calculus function =
  (i j : Fin n) ->
  ContinuousVectorFunction reals
    (partialDerivative reals calculus
      (partialDerivative reals calculus function i)
      j)

HasContinuousSecondPartials :
  {n : Nat} {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealCalculus reals ->
  (Vector n R -> R) ->
  Set
HasContinuousSecondPartials reals calculus function =
  FirstPartialsExist reals function
  and
  FirstPartialsContinuous reals calculus function
  and
  SecondPartialsExist reals calculus function
  and
  SecondPartialsContinuous reals calculus function

FunctionEqual :
  {A B : Set} ->
  (A -> B) ->
  (A -> B) ->
  Set
FunctionEqual {A} f g =
  (x : A) ->
  f x == g x

IsLinearFunction :
  {n : Nat} {R : Set} ->
  CompleteOrderedRealField R ->
  (Vector n R -> R) ->
  Set
IsLinearFunction {n} {R} reals function =
  ((x y : Vector n R) ->
    function (addVector reals x y) ==
    add reals (function x) (function y))
  and
  ((scalar : R) ->
    (x : Vector n R) ->
    function (scaleVector reals scalar x) ==
    multiply reals scalar (function x))

ConstantSkewPartialDifferences :
  {n : Nat} {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealCalculus reals ->
  (Fin n -> Vector n R -> R) ->
  Set
ConstantSkewPartialDifferences {n} {R} reals calculus f =
  Exists (Fin n -> Fin n -> R)
    (\ constants ->
      (i j : Fin n) ->
      (x : Vector n R) ->
      subtract reals
        (partialDerivative reals calculus (f i) j x)
        (partialDerivative reals calculus (f j) i x)
      ==
      constants i j)

CorrectedComponent :
  {n : Nat} {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealCalculus reals ->
  (Fin n -> Vector n R -> R) ->
  (Vector n R -> R) ->
  Fin n ->
  Vector n R ->
  R
CorrectedComponent reals calculus f g i x =
  add reals
    (f i x)
    (partialDerivative reals calculus g i x)

putnam-1986-a5 : Set1
putnam-1986-a5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (calculus : StandardRealCalculus reals) ->
  (n : Nat) ->
  Positive n ->
  (f : Fin n -> Vector n R -> R) ->
  ((i : Fin n) ->
    HasContinuousSecondPartials reals calculus (f i)) ->
  ConstantSkewPartialDifferences reals calculus f ->
  Exists (Vector n R -> R)
    (\ g ->
      (i : Fin n) ->
      IsLinearFunction reals
        (CorrectedComponent reals calculus f g i))
