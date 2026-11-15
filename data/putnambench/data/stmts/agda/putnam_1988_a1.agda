-- Statement-only formalization of PutnamBench corpus artifact putnam_1988_a1:
-- the planar region satisfying |x| - |y| <= 1 and |y| <= 1 has Lebesgue
-- area six. This file contains no proof.

{-# OPTIONS --safe #-}

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

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

Region : Set -> Set1
Region R =
  Point R -> Set

AbsoluteValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
AbsoluteValue reals x absolute =
  (lessOrEqual reals (zeroR reals) x and absolute == x)
  or
  (lessOrEqual reals x (zeroR reals) and
    absolute == negate reals x)

targetRegion :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Region R
targetRegion {R} reals p =
  Exists R
    (\ absolute-x ->
      AbsoluteValue reals (x-coordinate p) absolute-x
      and
      Exists R
        (\ absolute-y ->
          AbsoluteValue reals (y-coordinate p) absolute-y
          and
          lessOrEqual reals
            (subtract reals absolute-x absolute-y)
            (oneR reals)
          and
          lessOrEqual reals
            absolute-y
            (oneR reals)))

record Rectangle (R : Set) : Set where
  constructor rectangle
  field
    lower-x upper-x : R
    lower-y upper-y : R

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
  StrictLess reals (lower-x box) (x-coordinate p)
  and
  StrictLess reals (x-coordinate p) (upper-x box)
  and
  StrictLess reals (lower-y box) (y-coordinate p)
  and
  StrictLess reals (y-coordinate p) (upper-y box)

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
Covers {R} reals cover body =
  (p : Point R) ->
  body p ->
  Exists Nat
    (\ n -> RectangleContains reals (cover n) p)

coverPartialArea :
  {R : Set} ->
  CompleteOrderedRealField R ->
  RectangleCover R ->
  Nat ->
  R
coverPartialArea reals cover zero =
  rectangleArea reals (cover zero)
coverPartialArea reals cover (suc n) =
  add reals
    (coverPartialArea reals cover n)
    (rectangleArea reals (cover (suc n)))

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
        (subtract reals limit epsilon)
        (sequence n)
      and
      StrictLess reals
        (sequence n)
        (add reals limit epsilon))

CoverTotal :
  {R : Set} ->
  CompleteOrderedRealField R ->
  RectangleCover R ->
  R ->
  Set
CoverTotal reals cover total =
  SequentialLimit reals
    (coverPartialArea reals cover)
    total

CoverCost :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Region R ->
  R ->
  Set
CoverCost {R} reals body total =
  Exists (RectangleCover R)
    (\ cover ->
      ValidCover reals cover
      and
      Covers reals cover body
      and
      CoverTotal reals cover total)

LowerBound :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> Set) ->
  R ->
  Set
LowerBound reals values bound =
  (value : _) ->
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
LebesgueOuterArea reals body area =
  GreatestLowerBound reals (CoverCost reals body) area

six : Nat
six =
  suc (suc (suc (suc (suc (suc zero)))))

module Putnam1988A1Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  proposition : Set
  proposition =
    LebesgueOuterArea reals
      (targetRegion reals)
      (fromNat reals six)

putnam-1988-a1 : Set1
putnam-1988-a1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1988A1Statement.proposition reals
