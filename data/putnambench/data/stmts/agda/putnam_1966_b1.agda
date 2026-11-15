-- Statement-only formalization of PutnamBench corpus artifact putnam_1966_b1:
-- a convex polygon contained in the unit square has sum of squared side
-- lengths at most four. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1966B1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_
infix 4 _<=N_
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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

weakenFin : {n : Nat} -> Fin n -> Fin (suc n)
weakenFin {zero} ()
weakenFin {suc n} fzero =
  fzero
weakenFin {suc n} (fsuc i) =
  fsuc (weakenFin i)

advanceTail :
  {n : Nat} ->
  Fin (suc n) ->
  Fin (suc (suc n))
advanceTail {zero} fzero =
  fzero
advanceTail {suc n} fzero =
  fsuc (fsuc fzero)
advanceTail {suc n} (fsuc i) =
  fsuc (advanceTail i)

nextFin : {n : Nat} -> Fin n -> Fin n
nextFin {zero} ()
nextFin {suc zero} fzero =
  fzero
nextFin {suc (suc n)} fzero =
  fsuc fzero
nextFin {suc (suc n)} (fsuc i) =
  advanceTail i

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

four : Nat
four = suc three

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

Nonnegative :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
Nonnegative reals x =
  lessOrEqual reals (zeroR reals) x

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

PointEqual :
  {R : Set} ->
  Point R ->
  Point R ->
  Set
PointEqual p q =
  x-coordinate p == x-coordinate q
  and
  y-coordinate p == y-coordinate q

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

sumFin :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin reals {zero} values =
  zeroR reals
sumFin reals {suc n} values =
  add reals
    (values fzero)
    (sumFin reals (\ i -> values (fsuc i)))

weightedPoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  (Fin n -> Point R) ->
  Point R
weightedPoint reals weights vertices =
  point
    (sumFin reals
      (\ i ->
        multiply reals
          (weights i)
          (x-coordinate (vertices i))))
    (sumFin reals
      (\ i ->
        multiply reals
          (weights i)
          (y-coordinate (vertices i))))

ConvexHull :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> Point R) ->
  Point R ->
  Set
ConvexHull {R} reals {n} vertices p =
  Exists (Fin n -> R)
    (\ weights ->
      ((i : Fin n) -> Nonnegative reals (weights i))
      and
      sumFin reals weights == oneR reals
      and
      PointEqual p (weightedPoint reals weights vertices))

affinePoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Point R ->
  Point R ->
  Point R
affinePoint reals t p q =
  point
    (add reals
      (multiply reals
        (subtract reals (oneR reals) t)
        (x-coordinate p))
      (multiply reals t (x-coordinate q)))
    (add reals
      (multiply reals
        (subtract reals (oneR reals) t)
        (y-coordinate p))
      (multiply reals t (y-coordinate q)))

ClosedSegment :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  Set
ClosedSegment {R} reals p q x =
  Exists R
    (\ t ->
      lessOrEqual reals (zeroR reals) t
      and
      lessOrEqual reals t (oneR reals)
      and
      PointEqual x (affinePoint reals t p q))

InteriorOfConvexHull :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> Point R) ->
  Point R ->
  Set
InteriorOfConvexHull {R} reals vertices p =
  Exists R
    (\ epsilon ->
      StrictLess reals (zeroR reals) epsilon
      and
      ((q : Point R) ->
        StrictLess reals (distance reals p q) epsilon ->
        ConvexHull reals vertices q))

VerticesInUnitSquare :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> Point R) ->
  Set
VerticesInUnitSquare reals {n = n} vertices =
  (i : Fin n) ->
  lessOrEqual reals (zeroR reals) (x-coordinate (vertices i))
  and
  lessOrEqual reals (x-coordinate (vertices i)) (oneR reals)
  and
  lessOrEqual reals (zeroR reals) (y-coordinate (vertices i))
  and
  lessOrEqual reals (y-coordinate (vertices i)) (oneR reals)

PairwiseNoncollinear :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> Point R) ->
  Set
PairwiseNoncollinear reals {n = n} vertices =
  (i j k : Fin n) ->
  i != j ->
  j != k ->
  k != i ->
  Not (Collinear reals (vertices i) (vertices j) (vertices k))

EdgesAvoidInterior :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> Point R) ->
  Set
EdgesAvoidInterior {R} reals {n} vertices =
  (i : Fin n) ->
  (x : Point R) ->
  ClosedSegment reals (vertices i) (vertices (nextFin i)) x ->
  InteriorOfConvexHull reals vertices x ->
  Bottom

sumSquaredSideLengths :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> Point R) ->
  R
sumSquaredSideLengths reals vertices =
  sumFin reals
    (\ i ->
      squaredDistance reals
        (vertices i)
        (vertices (nextFin i)))

module Putnam1966B1Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  proposition : Set
  proposition =
    (n : Nat) ->
    three <=N n ->
    (vertices : Fin n -> Point R) ->
    VerticesInUnitSquare reals vertices ->
    PairwiseNoncollinear reals vertices ->
    EdgesAvoidInterior reals vertices ->
    lessOrEqual reals
      (sumSquaredSideLengths reals vertices)
      (fromNat reals four)

putnam-1966-b1 : Set1
putnam-1966-b1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1966B1Statement.proposition reals
