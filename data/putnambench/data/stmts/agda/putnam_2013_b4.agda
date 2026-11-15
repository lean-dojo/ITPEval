-- Statement-only formalization of PutnamBench corpus artifact putnam_2013_b4
-- (putnambench__agda__putnam_2013_b4): the variance bound for the product of
-- two continuous real functions on the unit interval. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

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
      (x : R) ->
      lessOrEqual zeroR (absoluteValue x)
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
        (\ n -> lessOrEqual x (fromNat n))
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

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

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

square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiply reals x x

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

Distance :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
Distance reals x y =
  absoluteValue reals (subtract reals x y)

InUnitInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
InUnitInterval reals x =
  lessOrEqual reals (zeroR reals) x
  and
  lessOrEqual reals x (oneR reals)

ContinuousOnUnitInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Set
ContinuousOnUnitInterval {R} reals f =
  (x : R) ->
  InUnitInterval reals x ->
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((y : R) ->
        InUnitInterval reals y ->
        StrictLess reals (Distance reals y x) delta ->
        StrictLess reals
          (Distance reals (f y) (f x))
          epsilon))

sumFirst :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero term =
  zeroR reals
sumFirst reals (suc n) term =
  add reals
    (sumFirst reals n term)
    (term n)

midpoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  Nat ->
  R
midpoint reals pieces index =
  multiply reals
    (add reals
      (fromNat reals index)
      (divide reals
        (oneR reals)
        (fromNat reals twoN)))
    (divide reals
      (oneR reals)
      (fromNat reals pieces))

midpointSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Nat ->
  R
midpointSum reals f pieces =
  multiply reals
    (divide reals
      (oneR reals)
      (fromNat reals pieces))
    (sumFirst reals pieces
      (\ index ->
        f (midpoint reals pieces index)))

SequentialLimit :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
SequentialLimit {R} reals sequence limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLess reals
        (Distance reals (sequence n) limit)
        epsilon)

UnitIntervalIntegralValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  Set
UnitIntervalIntegralValue reals f integral =
  SequentialLimit reals
    (\ n -> midpointSum reals f (suc n))
    integral

IsMaximumAbsoluteValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  Set
IsMaximumAbsoluteValue {R} reals f maximum =
  Exists R
    (\ point ->
      InUnitInterval reals point
      and
      absoluteValue reals (f point) == maximum)
  and
  ((x : R) ->
    InUnitInterval reals x ->
    lessOrEqual reals
      (absoluteValue reals (f x))
      maximum)

centeredSquare :
  {R : Set} ->
  CompleteOrderedRealField R ->
  ((R -> R) -> R) ->
  (R -> R) ->
  R ->
  R
centeredSquare reals mu f x =
  square reals
    (subtract reals (f x) (mu f))

pointwiseProduct :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  (R -> R) ->
  R ->
  R
pointwiseProduct reals f g x =
  multiply reals (f x) (g x)

Putnam2013B4 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Set
Putnam2013B4 {R} reals =
  (mu variance maximum : (R -> R) -> R) ->
  ((f : R -> R) ->
    ContinuousOnUnitInterval reals f ->
    UnitIntervalIntegralValue reals f (mu f)) ->
  ((f : R -> R) ->
    ContinuousOnUnitInterval reals f ->
    UnitIntervalIntegralValue reals
      (centeredSquare reals mu f)
      (variance f)) ->
  ((f : R -> R) ->
    ContinuousOnUnitInterval reals f ->
    IsMaximumAbsoluteValue reals f (maximum f)) ->
  (f g : R -> R) ->
  ContinuousOnUnitInterval reals f ->
  ContinuousOnUnitInterval reals g ->
  lessOrEqual reals
    (variance (pointwiseProduct reals f g))
    (add reals
      (multiply reals
        (multiply reals
          (fromNat reals twoN)
          (variance f))
        (square reals (maximum g)))
      (multiply reals
        (multiply reals
          (fromNat reals twoN)
          (variance g))
        (square reals (maximum f))))

putnam-2013-b4 : Set1
putnam-2013-b4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2013B4 reals
