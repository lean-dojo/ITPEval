-- Statement-only formalization of PutnamBench corpus artifact putnam_1989_b1
-- (putnambench__agda__putnam_1989_b1): the area probability that a point in
-- the unit square is nearer its center than every boundary point, expressed
-- as (4 * sqrt 2 - 5) / 3. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1989B1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

record Top : Set where
  constructor top

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

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

fourN : Nat
fourN =
  suc threeN

fiveN : Nat
fiveN =
  suc fourN

negativeNat : Nat -> Int
negativeNat zero =
  pos zero
negativeNat (suc n) =
  negsuc n

differenceNat : Nat -> Nat -> Int
differenceNat zero zero =
  pos zero
differenceNat (suc m) zero =
  pos (suc m)
differenceNat zero (suc n) =
  negsuc n
differenceNat (suc m) (suc n) =
  differenceNat m n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  differenceNat m (suc n)
addInt (negsuc m) (pos n) =
  differenceNat n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negativeNat (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negativeNat (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

fromInt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

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
sumFirst reals zero term =
  zeroR reals
sumFirst reals (suc n) term =
  add reals
    (sumFirst reals n term)
    (term n)

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

record StandardSquareRoot
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    squareRoot : R -> R

    square-root-nonnegative :
      (x : R) ->
      lessOrEqual reals (zeroR reals) (squareRoot x)
    square-root-square :
      (x : R) ->
      lessOrEqual reals (zeroR reals) x ->
      square reals (squareRoot x) == x
    square-root-nonpositive :
      (x : R) ->
      lessOrEqual reals x (zeroR reals) ->
      squareRoot x == zeroR reals
    square-root-unique :
      (x y : R) ->
      lessOrEqual reals (zeroR reals) y ->
      square reals y == x ->
      squareRoot x == y

open StandardSquareRoot

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

Region : Set -> Set1
Region R =
  Point R -> Set

record Rectangle (R : Set) : Set where
  constructor rectangle
  field
    lower-x : R
    upper-x : R
    lower-y : R
    upper-y : R

open Rectangle

ValidRectangle :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Rectangle R ->
  Set
ValidRectangle reals box =
  lessOrEqual reals (lower-x box) (upper-x box)
  and
  lessOrEqual reals (lower-y box) (upper-y box)

RectangleContains :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Rectangle R ->
  Point R ->
  Set
RectangleContains reals box p =
  lessOrEqual reals (lower-x box) (x-coordinate p)
  and
  lessOrEqual reals (x-coordinate p) (upper-x box)
  and
  lessOrEqual reals (lower-y box) (y-coordinate p)
  and
  lessOrEqual reals (y-coordinate p) (upper-y box)

rectangleArea :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Rectangle R ->
  R
rectangleArea reals box =
  multiply reals
    (subtract reals (upper-x box) (lower-x box))
    (subtract reals (upper-y box) (lower-y box))

RectangleCover : Set -> Set
RectangleCover R =
  Nat -> Rectangle R

ValidCover :
  {R : Set} ->
  CompleteOrderedRealField R ->
  RectangleCover R ->
  Set
ValidCover reals cover =
  (n : Nat) ->
  ValidRectangle reals (cover n)

Covers :
  {R : Set} ->
  CompleteOrderedRealField R ->
  RectangleCover R ->
  Region R ->
  Set
Covers {R} reals cover region =
  (p : Point R) ->
  region p ->
  Exists Nat
    (\ n -> RectangleContains reals (cover n) p)

CoverHasCost :
  {R : Set} ->
  CompleteOrderedRealField R ->
  RectangleCover R ->
  R ->
  Set
CoverHasCost reals cover total =
  SeriesHasSum reals
    (\ n -> rectangleArea reals (cover n))
    total

CoverCost :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Region R ->
  R ->
  Set
CoverCost {R} reals region total =
  Exists (RectangleCover R)
    (\ cover ->
      ValidCover reals cover
      and
      Covers reals cover region
      and
      CoverHasCost reals cover total)

LowerBound :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> Set) ->
  R ->
  Set
LowerBound {R} reals values bound =
  (value : R) ->
  values value ->
  lessOrEqual reals bound value

GreatestLowerBound :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> Set) ->
  R ->
  Set
GreatestLowerBound {R} reals values infimum =
  LowerBound reals values infimum
  and
  ((bound : R) ->
    LowerBound reals values bound ->
    lessOrEqual reals bound infimum)

LebesgueOuterArea :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Region R ->
  R ->
  Set
LebesgueOuterArea reals region area =
  GreatestLowerBound reals (CoverCost reals region) area

BoundedRegion :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Region R ->
  Set
BoundedRegion {R} reals region =
  Exists R
    (\ bound ->
      lessOrEqual reals (zeroR reals) bound
      and
      ((p : Point R) ->
        region p ->
        lessOrEqual reals
          (negate reals bound)
          (x-coordinate p)
        and
        lessOrEqual reals
          (x-coordinate p)
          bound
        and
        lessOrEqual reals
          (negate reals bound)
          (y-coordinate p)
        and
        lessOrEqual reals
          (y-coordinate p)
          bound))

record StandardLebesguePlane
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    area : Region R -> R
    area-characterization :
      (region : Region R) ->
      BoundedRegion reals region ->
      LebesgueOuterArea reals region (area region)

open StandardLebesguePlane

squaredDistance :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  R
squaredDistance reals p q =
  add reals
    (square reals
      (subtract reals (x-coordinate p) (x-coordinate q)))
    (square reals
      (subtract reals (y-coordinate p) (y-coordinate q)))

distance :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardSquareRoot reals ->
  Point R ->
  Point R ->
  R
distance reals roots p q =
  squareRoot roots (squaredDistance reals p q)

record Quadruple (A : Set) : Set where
  constructor quadruple
  field
    first-coordinate  : A
    second-coordinate : A
    third-coordinate  : A
    fourth-coordinate : A

open Quadruple

PositiveInt : Int -> Set
PositiveInt (pos zero) =
  Bottom
PositiveInt (pos (suc n)) =
  Top
PositiveInt (negsuc n) =
  Bottom

IntDivides : Int -> Int -> Set
IntDivides divisor dividend =
  Exists Int
    (\ factor -> multiplyInt divisor factor == dividend)

IsIntegerSquare : Int -> Set
IsIntegerSquare z =
  Exists Int
    (\ root -> multiplyInt root root == z)

IsUnit : Int -> Set
IsUnit (pos oneN) =
  Top
IsUnit (negsuc zero) =
  Top
IsUnit _ =
  Bottom

CoprimeTriple : Int -> Int -> Int -> Set
CoprimeTriple a c d =
  (common : Int) ->
  IntDivides common a ->
  IntDivides common c ->
  IntDivides common d ->
  IsUnit common

module Putnam1989B1Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (roots : StandardSquareRoot reals)
  (lebesgue : StandardLebesguePlane reals) where

  half : R
  half =
    divide reals
      (oneR reals)
      (fromNat reals twoN)

  center : Point R
  center =
    point half half

  unitSquare : Region R
  unitSquare p =
    lessOrEqual reals (zeroR reals) (x-coordinate p)
    and
    lessOrEqual reals (x-coordinate p) (oneR reals)
    and
    lessOrEqual reals (zeroR reals) (y-coordinate p)
    and
    lessOrEqual reals (y-coordinate p) (oneR reals)

  boundary : Region R
  boundary p =
    unitSquare p
    and
    ((x-coordinate p == zeroR reals)
      or
      (x-coordinate p == oneR reals)
      or
      (y-coordinate p == zeroR reals)
      or
      (y-coordinate p == oneR reals))

  closerToCenter : Region R
  closerToCenter p =
    unitSquare p
    and
    ((q : Point R) ->
      boundary q ->
      StrictLess reals
        (distance reals roots p center)
        (distance reals roots p q))

  solution : Quadruple Int
  solution =
    quadruple
      (pos fourN)
      (pos twoN)
      (negsuc fourN)
      (pos threeN)

  normalizedSolution : Set
  normalizedSolution =
    PositiveInt (second-coordinate solution)
    and
    PositiveInt (fourth-coordinate solution)
    and
    Not (IsIntegerSquare (second-coordinate solution))
    and
    CoprimeTriple
      (first-coordinate solution)
      (third-coordinate solution)
      (fourth-coordinate solution)

  answer : R
  answer =
    divide reals
      (add reals
        (multiply reals
          (fromInt reals (first-coordinate solution))
          (squareRoot roots
            (fromInt reals (second-coordinate solution))))
        (fromInt reals (third-coordinate solution)))
      (fromInt reals (fourth-coordinate solution))

  probability : R
  probability =
    divide reals
      (area lebesgue closerToCenter)
      (area lebesgue unitSquare)

  proposition : Set
  proposition =
    normalizedSolution
    and
    probability == answer

putnam-1989-b1 : Set1
putnam-1989-b1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (roots : StandardSquareRoot reals) ->
  (lebesgue : StandardLebesguePlane reals) ->
  Putnam1989B1Statement.proposition reals roots lebesgue
