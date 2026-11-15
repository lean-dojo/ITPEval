-- Statement-only formalization of PutnamBench corpus artifact putnam_2006_a1
-- (putnambench__agda__putnam_2006_a1): the Lebesgue volume of the real
-- polynomial region (x^2+y^2+z^2+8)^2 <= 36(x^2+y^2) is 6*pi^2.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2006A1 where

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
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

Predicate : Set -> Set1
Predicate A =
  A -> Set

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

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

fourN : Nat
fourN =
  twoN * twoN

sixN : Nat
sixN =
  suc (suc fourN)

eightN : Nat
eightN =
  twoN * fourN

thirtySixN : Nat
thirtySixN =
  sixN * sixN

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

ConvergesTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
ConvergesTo reals sequence limit =
  (epsilon : _) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      CloseTo reals limit epsilon (sequence n))

SeriesHasSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
SeriesHasSum reals terms total =
  ConvergesTo reals
    (\ n -> sumFirst reals n terms)
    total

alternatingSign :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
alternatingSign reals zero =
  oneR reals
alternatingSign reals (suc n) =
  negate reals (alternatingSign reals n)

piTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
piTerm reals n =
  multiply reals
    (fromNat reals fourN)
    (divide reals
      (alternatingSign reals n)
      (fromNat reals (twoN * n + oneN)))

PiValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
PiValue reals pi =
  SeriesHasSum reals (piTerm reals) pi

record Point3 (R : Set) : Set where
  constructor point3
  field
    xCoordinate : R
    yCoordinate : R
    zCoordinate : R

open Point3

record Box3
  {R : Set}
  (reals : CompleteOrderedRealField R) : Set where
  constructor box3
  field
    lowerX upperX : R
    lowerY upperY : R
    lowerZ upperZ : R
    validX : lessOrEqual reals lowerX upperX
    validY : lessOrEqual reals lowerY upperY
    validZ : lessOrEqual reals lowerZ upperZ

open Box3

BoxContains :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  Box3 reals ->
  Point3 R ->
  Set
BoxContains reals box point =
  lessOrEqual reals (lowerX box) (xCoordinate point)
  and
  lessOrEqual reals (xCoordinate point) (upperX box)
  and
  lessOrEqual reals (lowerY box) (yCoordinate point)
  and
  lessOrEqual reals (yCoordinate point) (upperY box)
  and
  lessOrEqual reals (lowerZ box) (zCoordinate point)
  and
  lessOrEqual reals (zCoordinate point) (upperZ box)

BoxVolume :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  Box3 reals ->
  R
BoxVolume reals box =
  multiply reals
    (subtract reals (upperX box) (lowerX box))
    (multiply reals
      (subtract reals (upperY box) (lowerY box))
      (subtract reals (upperZ box) (lowerZ box)))

record BoxCover
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (region : Predicate (Point3 R)) : Set1 where
  field
    coverBox :
      Nat ->
      Box3 reals
    covers :
      (point : Point3 R) ->
      region point ->
      Exists Nat
        (\ n ->
          BoxContains reals (coverBox n) point)

open BoxCover

CoverHasCost :
  {R : Set} ->
  {reals : CompleteOrderedRealField R} ->
  {region : Predicate (Point3 R)} ->
  BoxCover reals region ->
  R ->
  Set
CoverHasCost {reals = reals} cover cost =
  SeriesHasSum reals
    (\ n -> BoxVolume reals (coverBox cover n))
    cost

record IsLebesgueOuterVolume
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (region : Predicate (Point3 R))
  (volume : R) : Set1 where
  field
    lower-bound :
      (cover : BoxCover reals region) ->
      (cost : R) ->
      CoverHasCost cover cost ->
      lessOrEqual reals volume cost
    greatest-lower-bound :
      (lower : R) ->
      ((cover : BoxCover reals region) ->
        (cost : R) ->
        CoverHasCost cover cost ->
        lessOrEqual reals lower cost) ->
      lessOrEqual reals lower volume

module Putnam2006A1Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  region : Predicate (Point3 R)
  region point =
    let
      x = xCoordinate point
      y = yCoordinate point
      z = zCoordinate point
      radialSquare =
        add reals
          (square reals x)
          (square reals y)
      leftBase =
        add reals
          (add reals radialSquare (square reals z))
          (fromNat reals eightN)
    in
    lessOrEqual reals
      (square reals leftBase)
      (multiply reals
        (fromNat reals thirtySixN)
        radialSquare)

  answer : R -> R
  answer pi =
    multiply reals
      (fromNat reals sixN)
      (square reals pi)

  proposition : Set1
  proposition =
    (pi : R) ->
    PiValue reals pi ->
    IsLebesgueOuterVolume reals region (answer pi)

putnam-2006-a1 : Set1
putnam-2006-a1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2006A1Statement.proposition reals
