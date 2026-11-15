-- Statement-only formalization of PutnamBench corpus artifact putnam_2015_a1
-- (putnambench__agda__putnam_2015_a1): an area-maximizing point between two
-- points on the positive branch of xy = 1 makes the two chord-to-hyperbola
-- regions have equal area. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2015A1 where

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

ConvergesTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
ConvergesTo {R} reals sequence limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      CloseTo reals limit epsilon (sequence n))

maximum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
maximum reals x y with order-total reals x y
... | left _ =
  y
... | right _ =
  x

absoluteValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
absoluteValue reals x =
  maximum reals x (negate reals x)

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

OnPositiveHyperbola :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Set
OnPositiveHyperbola reals p =
  y-coordinate p ==
    divide reals
      (oneR reals)
      (x-coordinate p)
  and
  StrictLess reals
    (zeroR reals)
    (x-coordinate p)

doubleSignedArea :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  R
doubleSignedArea reals a b c =
  subtract reals
    (multiply reals
      (subtract reals
        (x-coordinate b)
        (x-coordinate a))
      (subtract reals
        (y-coordinate c)
        (y-coordinate a)))
    (multiply reals
      (subtract reals
        (y-coordinate b)
        (y-coordinate a))
      (subtract reals
        (x-coordinate c)
        (x-coordinate a)))

triangleArea :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  R
triangleArea reals a b c =
  divide reals
    (absoluteValue reals
      (doubleSignedArea reals a b c))
    (fromNat reals twoN)

chordLine :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  R ->
  R
chordLine reals p q x =
  add reals
    (multiply reals
      (divide reals
        (subtract reals
          (y-coordinate q)
          (y-coordinate p))
        (subtract reals
          (x-coordinate q)
          (x-coordinate p)))
      (subtract reals x (x-coordinate p)))
    (y-coordinate p)

sumFirst :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero terms =
  zeroR reals
sumFirst reals (suc n) terms =
  add reals
    (sumFirst reals n terms)
    (terms n)

midpointRiemannSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  (R -> R) ->
  Nat ->
  R
midpointRiemannSum reals lower upper function pieces =
  let
    step =
      divide reals
        (subtract reals upper lower)
        (fromNat reals pieces)
    halfStep =
      divide reals
        step
        (fromNat reals twoN)
  in
  sumFirst reals pieces
    (\ i ->
      multiply reals
        (function
          (add reals lower
            (add reals
              (multiply reals
                (fromNat reals i)
                step)
              halfStep)))
        step)

IntervalIntegralValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  (R -> R) ->
  R ->
  Set
IntervalIntegralValue reals lower upper function integralValue =
  ConvergesTo reals
    (\ n ->
      midpointRiemannSum reals
        lower
        upper
        function
        (suc n))
    integralValue

module Putnam2015A1Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  MaximalTriangleArea :
    Point R ->
    Point R ->
    Point R ->
    Set
  MaximalTriangleArea A B P =
    (P' : Point R) ->
    OnPositiveHyperbola reals P' ->
    StrictLess reals
      (x-coordinate A)
      (x-coordinate P') ->
    StrictLess reals
      (x-coordinate P')
      (x-coordinate B) ->
    lessOrEqual reals
      (triangleArea reals A P' B)
      (triangleArea reals A P B)

  chordMinusHyperbola :
    Point R ->
    Point R ->
    R ->
    R
  chordMinusHyperbola p q x =
    subtract reals
      (chordLine reals p q x)
      (divide reals (oneR reals) x)

  EqualRegionAreas :
    Point R ->
    Point R ->
    Point R ->
    Set
  EqualRegionAreas A B P =
    Exists R
      (\ commonArea ->
        IntervalIntegralValue reals
          (x-coordinate A)
          (x-coordinate P)
          (chordMinusHyperbola A P)
          commonArea
        and
        IntervalIntegralValue reals
          (x-coordinate P)
          (x-coordinate B)
          (chordMinusHyperbola P B)
          commonArea)

  proposition : Set
  proposition =
    (A B P : Point R) ->
    OnPositiveHyperbola reals A ->
    OnPositiveHyperbola reals B ->
    StrictLess reals
      (x-coordinate A)
      (x-coordinate B) ->
    OnPositiveHyperbola reals P ->
    StrictLess reals
      (x-coordinate A)
      (x-coordinate P) ->
    StrictLess reals
      (x-coordinate P)
      (x-coordinate B) ->
    MaximalTriangleArea A B P ->
    EqualRegionAreas A B P

putnam-2015-a1 : Set1
putnam-2015-a1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2015A1Statement.proposition reals
