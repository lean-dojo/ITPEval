-- Statement-only formalization of PutnamBench corpus artifact putnam_1966_a5:
-- every linear operator on continuous real functions that preserves continuity
-- and is local on intervals is pointwise multiplication by a continuous function.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1966A5 where

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

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR inverseR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    oneR-not-zeroR :
      oneR != zeroR

    addR-commutative :
      (x y : R) -> addR x y == addR y x
    addR-associative :
      (x y z : R) -> addR (addR x y) z == addR x (addR y z)
    addR-zero :
      (x : R) -> addR x zeroR == x
    addR-inverse :
      (x : R) -> addR x (negateR x) == zeroR

    multiplyR-commutative :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiplyR-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)
    multiplyR-one :
      (x : R) -> multiplyR x oneR == x
    multiplyR-zero :
      (x : R) -> multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    inverseR-zero :
      inverseR zeroR == zeroR
    multiplyR-inverse :
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
    addR-order :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiplyR-nonnegative :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zeroR-less-than-oneR :
      lessOrEqualR zeroR oneR and zeroR != oneR

    fromNatR-zero :
      fromNatR zero == zeroR
    fromNatR-successor :
      (n : Nat) -> fromNatR (suc n) == addR (fromNatR n) oneR
    fromNatR-addition :
      (m n : Nat) ->
      fromNatR (m + n) == addR (fromNatR m) (fromNatR n)
    fromNatR-multiplication :
      (m n : Nat) ->
      fromNatR (m * n) == multiplyR (fromNatR m) (fromNatR n)
    fromNatR-injective :
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

open CompleteOrderedRealField

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  addR reals x (negateR reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqualR reals x y and x != y

CloseTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals (subtract reals center radius) x
  and
  StrictLess reals x (addR reals center radius)

ContinuousAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  Set
ContinuousAt {R} reals function point =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        CloseTo reals point delta x ->
        CloseTo reals (function point) epsilon (function x)))

Continuous :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Set
Continuous {R} reals function =
  (point : R) ->
  ContinuousAt reals function point

FunctionEqual :
  {A B : Set} ->
  (A -> B) ->
  (A -> B) ->
  Set
FunctionEqual {A} f g =
  (x : A) ->
  f x == g x

LinearCombination :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  (R -> R) ->
  (R -> R) ->
  R ->
  R
LinearCombination reals a b f g x =
  addR reals
    (multiplyR reals a (f x))
    (multiplyR reals b (g x))

PointwiseProduct :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  (R -> R) ->
  R ->
  R
PointwiseProduct reals f g x =
  multiplyR reals (f x) (g x)

InClosedInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
InClosedInterval reals lower upper x =
  lessOrEqualR reals lower x
  and
  lessOrEqualR reals x upper

module Putnam1966A5Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (T : (R -> R) -> (R -> R)) where

  MapsContinuousToContinuous : Set
  MapsContinuousToContinuous =
    (f : R -> R) ->
    Continuous reals f ->
    Continuous reals (T f)

  LinearOnContinuousFunctions : Set
  LinearOnContinuousFunctions =
    (a b : R) ->
    (f g : R -> R) ->
    Continuous reals f ->
    Continuous reals g ->
    FunctionEqual
      (T (LinearCombination reals a b f g))
      (LinearCombination reals a b (T f) (T g))

  LocalOnClosedIntervals : Set
  LocalOnClosedIntervals =
    (lower upper : R) ->
    lessOrEqualR reals lower upper ->
    (f g : R -> R) ->
    Continuous reals f ->
    Continuous reals g ->
    ((x : R) ->
      InClosedInterval reals lower upper x ->
      f x == g x) ->
    (x : R) ->
    InClosedInterval reals lower upper x ->
    T f x == T g x

  IsPointwiseMultiplier : Set
  IsPointwiseMultiplier =
    Exists (R -> R)
      (\ multiplier ->
        Continuous reals multiplier
        and
        ((g : R -> R) ->
          Continuous reals g ->
          FunctionEqual
            (T g)
            (PointwiseProduct reals multiplier g)))

putnam-1966-a5 : Set1
putnam-1966-a5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (T : (R -> R) -> (R -> R)) ->
  Putnam1966A5Statement.MapsContinuousToContinuous reals T ->
  Putnam1966A5Statement.LinearOnContinuousFunctions reals T ->
  Putnam1966A5Statement.LocalOnClosedIntervals reals T ->
  Putnam1966A5Statement.IsPointwiseMultiplier reals T
