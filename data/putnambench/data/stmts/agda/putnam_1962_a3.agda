-- Statement-only formalization of PutnamBench corpus artifact putnam_1962_a3:
-- the triangle cut out by three cevians of a real Euclidean triangle has the
-- stated area ratio when the side-division ratios are equal. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

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
    add multiply : R -> R -> R
    negate inverse squareRoot : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) -> add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z == multiply x (multiply y z)
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
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR
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
          ((x : R) -> P x -> lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqual x upper) ->
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

square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiply reals x x

two :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
two reals =
  add reals (oneR reals) (oneR reals)

half :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
half reals =
  inverse reals (two reals)

StrictPositive :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
StrictPositive reals x =
  lessOrEqual reals (zeroR reals) x and x != zeroR reals

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

affineCombination :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Point R ->
  Point R ->
  Point R
affineCombination reals coefficient p q =
  point
    (add reals
      (multiply reals coefficient (x-coordinate p))
      (multiply reals
        (subtract reals (oneR reals) coefficient)
        (x-coordinate q)))
    (add reals
      (multiply reals coefficient (y-coordinate p))
      (multiply reals
        (subtract reals (oneR reals) coefficient)
        (y-coordinate q)))

ClosedSegment :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  Set
ClosedSegment {R} reals p q x =
  Exists R
    (\ coefficient ->
      lessOrEqual reals (zeroR reals) coefficient
      and
      lessOrEqual reals coefficient (oneR reals)
      and
      x == affineCombination reals coefficient p q)

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
      (subtract reals (x-coordinate b) (x-coordinate a))
      (subtract reals (y-coordinate c) (y-coordinate a)))
    (multiply reals
      (subtract reals (y-coordinate b) (y-coordinate a))
      (subtract reals (x-coordinate c) (x-coordinate a)))

Collinear :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  Set
Collinear reals a b c =
  doubleSignedArea reals a b c == zeroR reals

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
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  R
distance reals p q =
  squareRoot reals (squaredDistance reals p q)

triangleArea :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  R
triangleArea reals a b c =
  multiply reals
    (half reals)
    (squareRoot reals
      (square reals (doubleSignedArea reals a b c)))

module Putnam1962A3Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  proposition : Set
  proposition =
    (A B C A' B' C' P Q R' : Point R) ->
    (k : R) ->
    StrictPositive reals k ->
    Not (Collinear reals A B C) ->
    (ClosedSegment reals B C A'
      and
      divide reals
        (distance reals C A')
        (distance reals A' B)
      == k) ->
    (ClosedSegment reals C A B'
      and
      divide reals
        (distance reals A B')
        (distance reals B' C)
      == k) ->
    (ClosedSegment reals A B C'
      and
      divide reals
        (distance reals B C')
        (distance reals C' A)
      == k) ->
    (ClosedSegment reals B B' P
      and
      ClosedSegment reals C C' P) ->
    (ClosedSegment reals C C' Q
      and
      ClosedSegment reals A A' Q) ->
    (ClosedSegment reals A A' R'
      and
      ClosedSegment reals B B' R') ->
    divide reals
      (triangleArea reals P Q R')
      (triangleArea reals A B C)
    ==
    divide reals
      (square reals (subtract reals k (oneR reals)))
      (add reals
        (add reals
          (square reals k)
          k)
        (oneR reals))

putnam-1962-a3 : Set1
putnam-1962-a3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1962A3Statement.proposition reals
