-- Statement-only formalization of PutnamBench corpus artifact putnam_1974_b1:
-- five unit-circle points maximize their total pairwise Euclidean distance
-- exactly when a cyclic reordering has equal positive edge lengths. This file
-- contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixr 3 _and_
infix 1 _iff_

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

record _iff_ (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

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

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

origin :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R
origin reals =
  point (zeroR reals) (zeroR reals)

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

data Fin5 : Set where
  i0 i1 i2 i3 i4 : Fin5

next5 : Fin5 -> Fin5
next5 i0 = i1
next5 i1 = i2
next5 i2 = i3
next5 i3 = i4
next5 i4 = i0

record Permutation5 : Set where
  constructor permutation
  field
    apply        : Fin5 -> Fin5
    applyInverse : Fin5 -> Fin5
    inverse-left :
      (i : Fin5) ->
      applyInverse (apply i) == i
    inverse-right :
      (i : Fin5) ->
      apply (applyInverse i) == i

open Permutation5

OnUnitCircle :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Fin5 -> Point R) ->
  Set
OnUnitCircle reals points =
  (i : Fin5) ->
  distance reals (points i) (origin reals) == oneR reals

totalPairwiseDistance :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Fin5 -> Point R) ->
  R
totalPairwiseDistance reals points =
  add reals
    (distance reals (points i0) (points i1))
    (add reals
      (distance reals (points i0) (points i2))
      (add reals
        (distance reals (points i0) (points i3))
        (add reals
          (distance reals (points i0) (points i4))
          (add reals
            (distance reals (points i1) (points i2))
            (add reals
              (distance reals (points i1) (points i3))
              (add reals
                (distance reals (points i1) (points i4))
                (add reals
                  (distance reals (points i2) (points i3))
                  (add reals
                    (distance reals (points i2) (points i4))
                    (distance reals (points i3) (points i4))))))))))

DistanceSumOfUnitConfiguration :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
DistanceSumOfUnitConfiguration {R} reals value =
  Exists (Fin5 -> Point R)
    (\ points ->
      OnUnitCircle reals points
      and
      value == totalPairwiseDistance reals points)

UpperBound :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> Set) ->
  R ->
  Set
UpperBound {R} reals values upper =
  (value : R) ->
  values value ->
  lessOrEqual reals value upper

IsLeastUpperBound :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> Set) ->
  R ->
  Set
IsLeastUpperBound {R} reals values supremum =
  UpperBound reals values supremum
  and
  ((upper : R) ->
    UpperBound reals values upper ->
    lessOrEqual reals supremum upper)

MaximizesPairwiseDistance :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Fin5 -> Point R) ->
  Set
MaximizesPairwiseDistance reals points =
  IsLeastUpperBound reals
    (DistanceSumOfUnitConfiguration reals)
    (totalPairwiseDistance reals points)

EqualPositiveCyclicEdges :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Fin5 -> Point R) ->
  Set
EqualPositiveCyclicEdges {R} reals points =
  Exists R
    (\ edgeLength ->
      StrictLess reals (zeroR reals) edgeLength
      and
      Exists Permutation5
        (\ ordering ->
          (i : Fin5) ->
          distance reals
            (points (apply ordering i))
            (points (apply ordering (next5 i)))
          ==
          edgeLength))

PairwiseDistinct :
  {R : Set} ->
  (Fin5 -> Point R) ->
  Set
PairwiseDistinct points =
  (i j : Fin5) ->
  i != j ->
  points i != points j

module Putnam1974B1Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  proposition : Set
  proposition =
    (points : Fin5 -> Point R) ->
    OnUnitCircle reals points ->
    (MaximizesPairwiseDistance reals points
      iff
      (PairwiseDistinct points
      and
      EqualPositiveCyclicEdges reals points))

putnam-1974-b1 : Set1
putnam-1974-b1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1974B1Statement.proposition reals
